import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_compare_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_9 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_12 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_11 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11)
    have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_13 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
    intro _raw_i3 h_11 _
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11)
    have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_14 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_15 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_16 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_17 : Litex.In _value_i7 (Litex.RPos (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_11 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_11 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_11 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_12)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_23 : Litex.In _value_i4 (Litex.R (M := M)) := h_14
  have h_32 : Litex.In _value_i5 (Litex.R (M := M)) := h_15
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5)) (h_2 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_11 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_11 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
      intro _raw_i3 h_11 _
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_11)
      have h_11 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_13)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_46 : Litex.In _value_i4 (Litex.R (M := M)) := h_14
  have h_55 : Litex.In _value_i6 (Litex.R (M := M)) := h_16
  exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _value_i6)) (h_7 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_1181 : Litex.In _value_i8 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_68 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i9 _value_i4 (M.real_subset_complex _ h_68) (M.real_subset_complex _ h_14));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i9 _value_i4 h_68 h_14))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i9 _value_i4 (M.real_subset_complex _ h_68) (M.real_subset_complex _ h_14));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i9 _value_i4 h_68 h_14)))) _value_i7))))), (by
  have h_1182 : (M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_68 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i9 _value_i4 (M.real_subset_complex _ h_68) (M.real_subset_complex _ h_14));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i9 _value_i4 h_68 h_14))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i9 _value_i4 (M.real_subset_complex _ h_68) (M.real_subset_complex _ h_14));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i9 _value_i4 h_68 h_14)))) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i8 _litex_builder).mp h_1181)).choose
        )
    )
  exact (by
    let _atomic_wd_1_0 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i8 h_12 h_1182 True.intro)
    let _atomic_wd_1_1 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i8 h_13 h_1182 True.intro)
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)
)), Litex.Le _value_i5 _value_i6 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_12 _Host_i2 _rep_i2 _value_i2 h_13 _Host_i4 _rep_i4 _value_i4 h_14 _Host_i5 _rep_i5 _value_i5 h_15 _Host_i6 _rep_i6 _value_i6 h_16 _Host_i7 _rep_i7 _value_i7 h_17 h_1 h_2 h_7
          have h_18 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i7 h_17)
                )
            )
          have h_19 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_18)
                )
            )
          have h_20 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_18) _litex_zero.symm)
                )
            )
          have h_1569 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_1568 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1568)
              have h_1568 : Litex.In _value_i3 (Litex.R (M := M)) := h_1568
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_1570 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
              intro _raw_i3 h_1568 _
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1568)
              have h_1568 : Litex.In _value_i3 (Litex.R (M := M)) := h_1568
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_1571 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_1572 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_1573 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_1574 : Litex.In _value_i7 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_17
                )
            )
          have h_1575 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i7 h_1574)
                )
            )
          have h_1576 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_1575)
                )
            )
          have h_1577 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_1575) _litex_zero.symm)
                )
            )
          have h_10 : Litex.Le _value_i5 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_3102 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_1568 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1568)
                          have h_1568 : Litex.In _value_i3 (Litex.R (M := M)) := h_1568
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_1568 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1568)
                                  have h_1568 : Litex.In _value_i3 (Litex.R (M := M)) := h_1568
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_1569)
                          )
                      )
                    have h_3103 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_3104 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3103
                          )
                      )
                    have h_3105 : Litex.In _value_i4 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1571
                          )
                      )
                    have h_3108 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                          intro _raw_i3 h_1568 _
                          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1568)
                          have h_1568 : Litex.In _value_i3 (Litex.R (M := M)) := h_1568
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                  intro _raw_i3 h_1568 _
                                  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1568)
                                  have h_1568 : Litex.In _value_i3 (Litex.R (M := M)) := h_1568
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))
                              exact h_1570)
                          )
                      )
                    have h_3109 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3103
                          )
                      )
                    have h_3110 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3103
                          )
                      )
                    have h_3111 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_3112 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i4 _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_3113 : Litex.HasFiniteFunctionLimit .both _value_i2 _value_i4 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_3114 : Litex.In _value_i7 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1574
                          )
                      )
                    have h_3206 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i7 h_3114)
                          )
                      )
                    have h_3207 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_3206)
                          )
                      )
                    have h_3208 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_3206) _litex_zero.symm)
                          )
                      )
                    have h_3119 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_5294 : Litex.In _value_i12 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_3213 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105)))) _value_i7))))), (by
                      have h_5295 : (M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_3213 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105)))) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_5294)).choose
                            )
                        )
                      exact Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i1 _value_i12 h_3102 h_5295 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True) _value_i2 _value_i12 h_3108 h_5295 True.intro)
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i12 _rep_i12 _value_i12 h_5294
                              have h_5295 : (M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_3213 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105)))) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_5294)).choose
                                    )
                                )
                              have h_5298 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i12) (Litex.denote _value_i4))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i12) (Litex.denote _value_i4))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i7) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_3213 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105)))) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_5294)).choose_spec
                                    )
                                )
                              have h_5296 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_3213 : Litex.In _value_i11 (Litex.R (M := M))) => (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105))))) (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_5295) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_5298)
                                    )
                                )
                              have h_5297 : Litex.Lt ((fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_3213 : Litex.In _value_i11 (Litex.R (M := M))) => (let _wd_1_0 := (Litex.sub _value_i11 _value_i4 (M.real_subset_complex _ h_3213) (M.real_subset_complex _ h_3105));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i11 _value_i4 h_3213 h_3105))))) (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_5295) _value_i7 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_5298)
                                    )
                                )
                              exact (h_7 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_5294)
                            )
                          )
                      )
                    have h_3120 : Litex.Le _value_i5 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show Litex.Le _value_i5 _value_i6 from (by
                              let _law0_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_1568 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1568)
                                have h_1568 : Litex.In _value_i3 (Litex.R (M := M)) := h_1568
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                              have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_3102
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
                                refine ⟨_law0_signature, _law0_member, ?_, h_3104⟩
                                intro x hx
                                exact h_3103 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                              let _law1_signature := ((let _checked_header : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → True := (by
                                intro _raw_i3 h_1568 _
                                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1568)
                                have h_1568 : Litex.In _value_i3 (Litex.R (M := M)) := h_1568
                                exact True.intro);
                              Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i3 : M.Value) => True)))).val
                              have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_3108
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
                                refine ⟨_law1_signature, _law1_member, ?_, h_3110⟩
                                intro x hx
                                exact h_3109 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                              have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                              exact Litex.finiteFunctionLimitCompare .both (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i4) (Litex.denote _value_i5) (Litex.denote _value_i6) (Litex.denote _law0_domain) _value_i7 h_3114 _law_domain_0 (_law_domain_1.symm.trans (h_3111.trans _law_domain_0)) h_3112 h_3113 (by
                                intro input hinput
                                exact h_3119 (Litex.semanticObject input (M.member_isSet hinput)) hinput
                              )
                            ))
                          )
                      )
                    exact h_3120
                  )
                )
            )
          exact h_10
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_compare_x2f_statement_x2e_lit
