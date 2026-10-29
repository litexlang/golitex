import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_squeeze_x2f_statement_x2e_lit

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
  exact Litex.HasFiniteFunctionLimit .both _value_i1 _value_i5 _value_i6)) (h_2 : (by
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
  exact Litex.HasFiniteFunctionLimit .both _value_i3 _value_i5 _value_i6)) (h_7 : ∀ (_value_i8 : Litex.Obj (M := M) M.Value) (h_1204 : Litex.In _value_i8 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_73 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i9 _value_i5 (M.real_subset_complex _ h_73) (M.real_subset_complex _ h_14));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i9 _value_i5 h_73 h_14))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i9 _value_i5 (M.real_subset_complex _ h_73) (M.real_subset_complex _ h_14));
(Litex.abs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR _value_i9 _value_i5 h_73 h_14)))) _value_i7))))), (by
  have h_1205 : (M.mem (Litex.denote _value_i8) (M.standard Litex.StandardSetValue.real)) :=
    (by
      litex_checked_step =>
        exact (
          ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_73 : Litex.In _value_i9 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i9 _value_i5 (M.real_subset_complex _ h_73) (M.real_subset_complex _ h_14));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i9 _value_i5 h_73 h_14))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i9 _value_i5 (M.real_subset_complex _ h_73) (M.real_subset_complex _ h_14));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR _value_i9 _value_i5 h_73 h_14)))) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i8 _litex_builder).mp h_1204)).choose
        )
    )
  exact ((Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i8 h_11 h_1205 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i8 h_12 h_1205 True.intro)) ∧ (Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i8 h_12 h_1205 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i8 h_13 h_1205 True.intro)))
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
  have h_1929 : Litex.In _value_i5 (Litex.R (M := M)) := h_14
  have h_1940 : Litex.In _value_i6 (Litex.R (M := M)) := h_15
  exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i5 _value_i6) :=
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
          have h_1954 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_1953 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
              have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_1955 : Litex.In _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_1953 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
              have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_1956 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
              intro _raw_i4 h_1953 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
              have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_1957 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_1958 : Litex.In _value_i6 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          have h_1959 : Litex.In _value_i7 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_16
                )
            )
          have h_1960 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i7 h_1959)
                )
            )
          have h_1961 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_1960)
                )
            )
          have h_1962 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_1960) _litex_zero.symm)
                )
            )
          have h_3894 : Litex.HasFiniteFunctionLimit .both _value_i2 _value_i5 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_3870 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_1953 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                          have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_1953 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                                  have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_1954)
                          )
                      )
                    have h_3871 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_3872 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3871
                          )
                      )
                    have h_3873 : Litex.In _value_i5 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1957
                          )
                      )
                    have h_3876 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_1953 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                          have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_1953 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                                  have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_1955)
                          )
                      )
                    have h_3877 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3871
                          )
                      )
                    have h_3878 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3871
                          )
                      )
                    have h_3879 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_3882 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                          intro _raw_i4 h_1953 _
                          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                          have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                                  intro _raw_i4 h_1953 _
                                  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                                  have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))
                              exact h_1956)
                          )
                      )
                    have h_3883 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3871
                          )
                      )
                    have h_3884 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3871
                          )
                      )
                    have h_3885 : Litex.Same (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (show @Eq M.Value _ _ from Eq.refl _)
                          )
                      )
                    have h_3886 : Litex.HasFiniteFunctionLimit .both _value_i1 _value_i5 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_3887 : Litex.HasFiniteFunctionLimit .both _value_i3 _value_i5 _value_i6 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_2
                          )
                      )
                    have h_3888 : Litex.In _value_i7 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1959
                          )
                      )
                    have h_4013 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i7 h_3888)
                          )
                      )
                    have h_4014 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_4013)
                          )
                      )
                    have h_4015 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_4013) _litex_zero.symm)
                          )
                      )
                    have h_3893 : ∀ {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_6505 : Litex.In _value_i12 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_4020 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                    (Litex.abs _wd_1_0 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873)))) _value_i7))))), (by
                      have h_6506 : (M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_4020 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873)))) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_6505)).choose
                            )
                        )
                      exact ((Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i1 _value_i12 h_3870 h_6506 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i12 h_3876 h_6506 True.intro)) ∧ (Litex.Le (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i2 _value_i12 h_3876 h_6506 True.intro) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True) _value_i3 _value_i12 h_3882 h_6506 True.intro)))
                    ) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i12 _rep_i12 _value_i12 h_6505
                              have h_6506 : (M.mem (Litex.denote _value_i12) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_4020 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873)))) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_6505)).choose
                                    )
                                )
                              have h_6509 : (((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i12) (Litex.denote _value_i5))) = M.number (_s : ℂ) ∧ _r < _s)) ∧ ((∃ (_r _s : ℝ), (Litex.absValue (M := M) (M.subValue (Litex.denote _value_i12) (Litex.denote _value_i5))) = M.number (_r : ℂ) ∧ (Litex.denote _value_i7) = M.number (_s : ℂ) ∧ _r < _s))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_4020 : Litex.In _value_i11 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873))))) ∧ (Litex.Lt (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                                      (Litex.abs _wd_1_0 (by
                                        let _atomic_wd_1_0 := _wd_1_0
                                        exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873)))) _value_i7)))); (Litex.inSetBuilderObj_iff _value_i12 _litex_builder).mp h_6505)).choose_spec
                                    )
                                )
                              have h_6507 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_4020 : Litex.In _value_i11 (Litex.R (M := M))) => (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873))))) (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_6506) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.left h_6509)
                                    )
                                )
                              have h_6508 : Litex.Lt ((fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_4020 : Litex.In _value_i11 (Litex.R (M := M))) => (let _wd_1_0 := (Litex.sub _value_i11 _value_i5 (M.real_subset_complex _ h_4020) (M.real_subset_complex _ h_3873));
                              (Litex.abs _wd_1_0 (by
                                let _atomic_wd_1_0 := _wd_1_0
                                exact (Litex.subInR _value_i11 _value_i5 h_4020 h_3873))))) (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_6506) _value_i7 :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (And.right h_6509)
                                    )
                                )
                              exact (h_7 (Litex.semanticObject (Litex.denote _value_i12) (Litex.isSet _value_i12)) h_6505)
                            )
                          )
                      )
                    exact (show (by
                    have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i2) := (show Litex.RealFunctionValue M (Litex.denote _value_i2) from by
                      let _limit_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_1953 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                        have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                      have _limit_function : Litex.In _value_i2 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i2 _value_i2 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_1953 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                        have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                        intro _raw_i4 h_1953 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                        have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                        exact True.intro);
                      Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_3876)
                      have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := h_3871
                      have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := h_3871
                      refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
                      intro x hx
                      exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    )
                    have h_8326 : Litex.In _value_i5 (Litex.R (M := M)) := h_3873
                    have h_8333 : Litex.In _value_i6 (Litex.R (M := M)) := h_1958
                    exact Litex.HasFiniteFunctionLimit .both _value_i2 _value_i5 _value_i6) from (by
                    let _law0_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_1953 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                      have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law0_member : Litex.In _value_i1 (Litex.fnSet _law0_signature) := h_3870
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
                      refine ⟨_law0_signature, _law0_member, ?_, h_3872⟩
                      intro x hx
                      exact h_3871 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_0 : Litex.denote _law0_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i1) := (_law0_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law0_signature.domain_isSet _law0_member).symm)
                    let _law1_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_1953 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                      have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law1_member : Litex.In _value_i2 (Litex.fnSet _law1_signature) := h_3876
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
                      refine ⟨_law1_signature, _law1_member, ?_, h_3878⟩
                      intro x hx
                      exact h_3877 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_1 : Litex.denote _law1_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i2) := (_law1_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law1_signature.domain_isSet _law1_member).symm)
                    let _law2_signature := ((let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → True := (by
                      intro _raw_i4 h_1953 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_1953)
                      have h_1953 : Litex.In _value_i4 (Litex.R (M := M)) := h_1953
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => True)))).val
                    have _law2_member : Litex.In _value_i3 (Litex.fnSet _law2_signature) := h_3882
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
                      refine ⟨_law2_signature, _law2_member, ?_, h_3884⟩
                      intro x hx
                      exact h_3883 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    have _law_domain_2 : Litex.denote _law2_domain = Litex.FunctionSemantics.domainValue (Litex.denote _value_i3) := (_law2_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _law2_signature.domain_isSet _law2_member).symm)
                    exact Litex.finiteFunctionLimitSqueeze .both (Litex.denote _value_i1) (Litex.denote _value_i2) (Litex.denote _value_i3) (Litex.denote _value_i5) (Litex.denote _value_i6) (Litex.denote _law0_domain) _value_i7 h_3888 _law_real_1 _law_domain_0 (_law_domain_1.symm.trans (h_3879.trans _law_domain_0)) (_law_domain_2.symm.trans (h_3885.trans _law_domain_0)) h_3886 h_3887 (by
                      intro input hinput
                      exact h_3893 (Litex.semanticObject input (M.member_isSet hinput)) hinput
                    )
                  ))
                  )
                )
            )
          exact h_3894
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_at_x5f_squeeze_x2f_statement_x2e_lit
