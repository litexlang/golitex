import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_squeeze_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_9 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
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
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_12 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_13 : Litex.In _value_i6 (Litex.R (M := M))) (h_1 : (by
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
  have h_16 : Litex.In _value_i5 (Litex.R (M := M)) := h_12
  exact Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i5)) (h_2 : (by
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
  have h_30 : Litex.In _value_i5 (Litex.R (M := M)) := h_12
  exact Litex.HasInfiniteFunctionLimit .positive _value_i3 _value_i5)) (h_5 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_91 : Litex.In _value_i7 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_41 : Litex.In _value_i8 (Litex.R (M := M))) => Litex.Lt _value_i6 _value_i8))), (by
  have h_92 : (M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_41 : Litex.In _value_i8 (Litex.R (M := M))) => Litex.Lt _value_i6 _value_i8)); (Litex.inSetBuilderObj_iff _value_i7 _litex_builder).mp h_91)).choose
        )
    )
  exact ((Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i7 h_9 h_92 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i7 h_10 h_92 True.intro)) ∧ (Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i7 h_10 h_92 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i7 h_11 h_92 True.intro)))
)), (by
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
  have h_740 : Litex.In _value_i5 (Litex.R (M := M)) := h_12
  exact Litex.HasInfiniteFunctionLimit .positive _value_i2 _value_i5) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_9 _Host_i2 _rep_i2 _value_i2 h_10 _Host_i3 _rep_i3 _value_i3 h_11 _Host_i5 _rep_i5 _value_i5 h_12 _Host_i6 _rep_i6 _value_i6 h_13 h_1 h_2 h_5
          have h_752 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_751 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
              have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_753 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_751 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
              have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_754 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_751 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
              have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_755 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_756 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_1502 : Litex.HasInfiniteFunctionLimit .positive _value_i2 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_1481 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_751 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                          have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_751 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                                  have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_752)
                          )
                      )
                    have h_1482 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_1483 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1482
                          )
                      )
                    have h_1486 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_751 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                          have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_751 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                                  have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_753)
                          )
                      )
                    have h_1487 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1482
                          )
                      )
                    have h_1488 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1482
                          )
                      )
                    have h_1489 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_1492 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_751 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                          have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_751 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                                  have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_754)
                          )
                      )
                    have h_1493 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1482
                          )
                      )
                    have h_1494 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1482
                          )
                      )
                    have h_1495 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_1496 : Litex.HasInfiniteFunctionLimit .positive _value_i1 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_1497 : Litex.HasInfiniteFunctionLimit .positive _value_i3 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_1498 : Litex.In _value_i6 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_756
                          )
                      )
                    have h_1501 : ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_1653 : Litex.In _value_i11 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1599 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt _value_i6 _value_i10))), (by
                      have h_1654 : (M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1599 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt _value_i6 _value_i10)); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_1653)).choose
                            )
                        )
                      exact ((Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i11 h_1481 h_1654 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i11 h_1486 h_1654 True.intro)) ∧ (Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i11 h_1486 h_1654 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i11 h_1492 h_1654 True.intro)))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i11 _rep_i11 _value_i11 h_1653
                              have h_1654 : (M.mem (Litex.denote _value_i11) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1599 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt _value_i6 _value_i10)); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_1653)).choose
                                    )
                                )
                              have h_1655 : (∃ (_r _s : ℝ), (Litex.denote _value_i6) = M.number (_r : ℂ) ∧ (Litex.denote _value_i11) = M.number (_s : ℂ) ∧ _r < _s) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1599 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.Lt _value_i6 _value_i10)); (Litex.inSetBuilderObj_iff _value_i11 _litex_builder).mp h_1653)).choose_spec
                                    )
                                )
                              exact (h_5 (Litex.semanticObject (Litex.denote _value_i11) (Litex.isSet _value_i11)) h_1653)
                            )
                          )
                      )
                    exact (show (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_751 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                        have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_751 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                        have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_751 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                        have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1486)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_1482
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_1482
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_3228 : Litex.In _value_i5 (Litex.R (M := M)) := h_755
                    exact Litex.HasInfiniteFunctionLimit .positive _value_i2 _value_i5) from (by
                    let _law0_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_751 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                      have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_1481
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
                      refine ⟨_law0_signature, _law0_member, ?_, h_1483⟩
                      intro x hx
                      exact h_1482 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                    let _law1_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_751 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                      have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_1486
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
                      refine ⟨_law1_signature, _law1_member, ?_, h_1488⟩
                      intro x hx
                      exact h_1487 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                    let _law2_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_751 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_751)
                      have h_751 : Litex.In _value_i4 (Litex.R (M := M)) := h_751
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law2_member : Litex.In _value_i3 (Litex.fnSet _law2_signature) := h_1492
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
                      refine ⟨_law2_signature, _law2_member, ?_, h_1494⟩
                      intro x hx
                      exact h_1493 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i3) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
                    exact Litex.infiniteFunctionLimitSqueeze .positive (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3) (Litex.denote _value_i5) (Litex.denote _law0_domain) _value_i6 h_1498 _law_real_1 _law_domain_0 (_law_domain_1.symm.trans (h_1489.trans _law_domain_0)) (_law_domain_2.symm.trans (h_1495.trans _law_domain_0)) h_1496 h_1497 (by
                      intro input hinput
                      exact h_1501 (Litex.semanticObject input (M.member_isSet hinput)) hinput
                    )
                  ))
                  )
                )
            )
          exact h_1502
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_pos_x5f_inf_x5f_squeeze_x2f_statement_x2e_lit
