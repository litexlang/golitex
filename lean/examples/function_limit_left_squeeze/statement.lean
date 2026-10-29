import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_squeeze_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_9 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_11 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_10 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_10 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_13 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
    intro _raw_i4 h_10 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
    have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_14 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_15 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_16 : Litex.In _value_i7 (Litex.RPos (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_11)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_22 : Litex.In _value_i5 (Litex.R (M := M)) := h_14
  have h_33 : Litex.In _value_i6 (Litex.R (M := M)) := h_15
  exact Litex.HasFiniteFunctionLimit .left _value_i1 _value_i5 _value_i6)) (h_2 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i3) := (show Litex.RealFunctionValue M (Litex.denote _value_i3) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i3 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i3 _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_13)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_49 : Litex.In _value_i5 (Litex.R (M := M)) := h_14
  have h_60 : Litex.In _value_i6 (Litex.R (M := M)) := h_15
  exact Litex.HasFiniteFunctionLimit .left _value_i3 _value_i5 _value_i6)) (h_7 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_634 : Litex.In _value_i8 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_73 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i5 _value_i9 (M.real_subset_complex _ h_14) (M.real_subset_complex _ h_73))) ∧ (Litex.Lt (Litex.sub _value_i5 _value_i9 (M.real_subset_complex _ h_14) (M.real_subset_complex _ h_73)) _value_i7))))), (by
  have h_635 : (M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_73 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i5 _value_i9 (M.real_subset_complex _ h_14) (M.real_subset_complex _ h_73))) ∧ (Litex.Lt (Litex.sub _value_i5 _value_i9 (M.real_subset_complex _ h_14) (M.real_subset_complex _ h_73)) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i8 _litex_builder).mp h_634)).choose
        )
    )
  exact ((Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i8 h_11 h_635 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i8 h_12 h_635 True.intro)) ∧ (Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i8 h_12 h_635 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_13 h_635 True.intro)))
)), (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
      intro _raw_i4 h_10 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10)
      have h_10 : Litex.In _value_i4 (Litex.R (M := M)) := h_10
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_12)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_1359 : Litex.In _value_i5 (Litex.R (M := M)) := h_14
  have h_1370 : Litex.In _value_i6 (Litex.R (M := M)) := h_15
  exact Litex.HasFiniteFunctionLimit .left _value_i2 _value_i5 _value_i6) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_11 _Host_i2 _rep_i2 _value_i2 h_12 _Host_i3 _rep_i3 _value_i3 h_13 _Host_i5 _rep_i5 _value_i5 h_14 _Host_i6 _rep_i6 _value_i6 h_15 _Host_i7 _rep_i7 _value_i7 h_16 h_1 h_2 h_7
          have h_17 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i7 h_16)
                )
            )
          have h_18 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_17)
                )
            )
          have h_19 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_17) _litex_zero.symm)
                )
            )
          have h_1384 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_1383 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
              have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_1385 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_1383 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
              have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_1386 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_1383 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
              have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_1387 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_1388 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_1389 : Litex.In _value_i7 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_1390 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i7 h_1389)
                )
            )
          have h_1391 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_1390)
                )
            )
          have h_1392 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_1390) _litex_zero.symm)
                )
            )
          have h_2754 : Litex.HasFiniteFunctionLimit .left _value_i2 _value_i5 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_2730 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_1383 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                          have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_1383 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                                  have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_1384)
                          )
                      )
                    have h_2731 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_2732 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2731
                          )
                      )
                    have h_2733 : Litex.In _value_i5 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1387
                          )
                      )
                    have h_2736 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_1383 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                          have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_1383 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                                  have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_1385)
                          )
                      )
                    have h_2737 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2731
                          )
                      )
                    have h_2738 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2731
                          )
                      )
                    have h_2739 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_2742 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_1383 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                          have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_1383 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                                  have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_1386)
                          )
                      )
                    have h_2743 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2731
                          )
                      )
                    have h_2744 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2731
                          )
                      )
                    have h_2745 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_2746 : Litex.HasFiniteFunctionLimit .left _value_i1 _value_i5 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_2747 : Litex.HasFiniteFunctionLimit .left _value_i3 _value_i5 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_2748 : Litex.In _value_i7 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1389
                          )
                      )
                    have h_2873 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i7 h_2748)
                          )
                      )
                    have h_2874 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_2873)
                          )
                      )
                    have h_2875 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_2873) _litex_zero.symm)
                          )
                      )
                    have h_2753 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_3991 : Litex.In _value_i12 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_2880 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880))) ∧ (Litex.Lt (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880)) _value_i7))))), (by
                      have h_3992 : (M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_2880 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880))) ∧ (Litex.Lt (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880)) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_3991)).choose
                            )
                        )
                      exact ((Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i12 h_2730 h_3992 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i12 h_2736 h_3992 True.intro)) ∧ (Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i12 h_2736 h_3992 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i12 h_2742 h_3992 True.intro)))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i12 _rep_i12 _value_i12 h_3991
                              have h_3992 : (M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_2880 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880))) ∧ (Litex.Lt (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880)) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_3991)).choose
                                    )
                                )
                              have h_3995 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.subValue (Litex.denote _value_i5) (Litex.denote _value_i12)) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (M.subValue (Litex.denote _value_i5) (Litex.denote _value_i12)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i7) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_2880 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880))) ∧ (Litex.Lt (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880)) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_3991)).choose_spec
                                    )
                                )
                              have h_3993 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_2880 : Litex.In _value_i11 (Litex.R (M := M))) => (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880))) (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_3992) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_3995)
                                    )
                                )
                              have h_3994 : Litex.Lt ((fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_2880 : Litex.In _value_i11 (Litex.R (M := M))) => (Litex.sub _value_i5 _value_i11 (M.real_subset_complex _ h_2733) (M.real_subset_complex _ h_2880))) (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_3992) _value_i7 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_3995)
                                    )
                                )
                              exact (h_7 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_3991)
                            )
                          )
                      )
                    exact (show (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_1383 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                        have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_1383 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                        have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_1383 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                        have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_2736)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_2731
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_2731
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_5812 : Litex.In _value_i5 (Litex.R (M := M)) := h_2733
                    have h_5819 : Litex.In _value_i6 (Litex.R (M := M)) := h_1388
                    exact Litex.HasFiniteFunctionLimit .left _value_i2 _value_i5 _value_i6) from (by
                    let _law0_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_1383 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                      have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_2730
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
                      refine ⟨_law0_signature, _law0_member, ?_, h_2732⟩
                      intro x hx
                      exact h_2731 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                    let _law1_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_1383 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                      have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_2736
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
                      refine ⟨_law1_signature, _law1_member, ?_, h_2738⟩
                      intro x hx
                      exact h_2737 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                    let _law2_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_1383 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1383)
                      have h_1383 : Litex.In _value_i4 (Litex.R (M := M)) := h_1383
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law2_member : Litex.In _value_i3 (Litex.fnSet _law2_signature) := h_2742
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
                      refine ⟨_law2_signature, _law2_member, ?_, h_2744⟩
                      intro x hx
                      exact h_2743 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i3) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
                    exact Litex.finiteFunctionLimitSqueeze .left (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3) (Litex.denote _value_i5) (Litex.denote _value_i6) (Litex.denote _law0_domain) _value_i7 h_2748 _law_real_1 _law_domain_0 (_law_domain_1.symm.trans (h_2739.trans _law_domain_0)) (_law_domain_2.symm.trans (h_2745.trans _law_domain_0)) h_2746 h_2747 (by
                      intro input hinput
                      exact h_2753 (Litex.semanticObject input (M.member_isSet hinput)) hinput
                    )
                  ))
                  )
                )
            )
          exact h_2754
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_squeeze_x2f_statement_x2e_lit
