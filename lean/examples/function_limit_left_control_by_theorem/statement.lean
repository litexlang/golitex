import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_control_x5f_by_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v3 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_9 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := h_9
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_11 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_12 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_13 : Litex.In _value_i5 (Litex.RPos (M := M))) (h_1 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := (show Litex.RealFunctionValue M (Litex.denote _value_i1) from by
    let _limit_signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_9 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := h_9
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
    have _limit_function : Litex.In _value_i1 (Litex.fnSet _limit_signature) := (Litex.inOfSame _value_i1 _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_9 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := h_9
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
      intro _raw_i2 h_9 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
      have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := h_9
      exact True.intro);
    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10)
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_19 : Litex.In _value_i3 (Litex.R (M := M)) := h_11
  have h_26 : Litex.In _value_i4 (Litex.R (M := M)) := h_12
  exact Litex.HasFiniteFunctionLimit .left _value_i1 _value_i3 _value_i4)), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_35 : Litex.In _value_i6 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i7 : Litex.Obj (M := M) M.Value) (h_39 : Litex.In _value_i7 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i7 (M.real_subset_complex _ h_11) (M.real_subset_complex _ h_39))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i7 (M.real_subset_complex _ h_11) (M.real_subset_complex _ h_39)) _value_i6)))) (let _wd_1_0 := _value_i1;
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_546 : Litex.In _value_i8 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i8 _value_i4 (M.real_subset_complex _ h_546) (M.real_subset_complex _ h_12));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i8 _value_i4 h_546 h_12)))) _value_i5));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_954 : Litex.In _value_i8 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i8 _value_i4 (M.real_subset_complex _ h_954) (M.real_subset_complex _ h_12));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i8 _value_i4 h_954 h_12)))) _value_i5))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_954 : Litex.In _value_i8 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i8 _value_i4 (M.real_subset_complex _ h_954) (M.real_subset_complex _ h_12));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i8 _value_i4 h_954 h_12)))) _value_i5))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_1362 : Litex.In _value_i10 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i10 h_10 h_1362 True.intro) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_9 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := h_9
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_9 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_9)
    have h_9 : Litex.In _value_i2 (Litex.R (M := M)) := h_9
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_10))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10 _Host_i3 _rep_i3 _value_i3 h_11 _Host_i4 _rep_i4 _value_i4 h_12 _Host_i5 _rep_i5 _value_i5 h_13 h_1
          have h_14 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i5 h_13)
                )
            )
          have h_15 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_14)
                )
            )
          have h_16 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_14) _litex_zero.symm)
                )
            )
          have h_1837 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_1836 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1836)
              have h_1836 : Litex.In _value_i2 (Litex.R (M := M)) := h_1836
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_1838 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_11
                )
            )
          have h_1839 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_1840 : Litex.In _value_i5 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_13
                )
            )
          have h_1841 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i5 h_1840)
                )
            )
          have h_1842 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_1841)
                )
            )
          have h_1843 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_1841) _litex_zero.symm)
                )
            )
          have h_1875 : ∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_4778 : Litex.In _value_i11 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_4782 : Litex.In _value_i12 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i12 (M.real_subset_complex _ h_1838) (M.real_subset_complex _ h_4782))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i12 (M.real_subset_complex _ h_1838) (M.real_subset_complex _ h_4782)) _value_i11)))) (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_5289 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_5289) (M.real_subset_complex _ h_1839));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR _value_i13 _value_i4 h_5289 h_1839)))) _value_i5));
          (by
            have _preimage_target : (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_5697 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_5697) (M.real_subset_complex _ h_1839));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i13 _value_i4 h_5697 h_1839)))) _value_i5))
            exact Litex.IsSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_5697 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_5697) (M.real_subset_complex _ h_1839));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i13 _value_i4 h_5697 h_1839)))) _value_i5))
            exact (Litex.isSet _atomic_wd_1_0))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_6105 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i17 h_1837 h_6105 True.intro) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_1836 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1836)
              have h_1836 : Litex.In _value_i2 (Litex.R (M := M)) := h_1836
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
              intro _raw_i2 h_1836 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1836)
              have h_1836 : Litex.In _value_i2 (Litex.R (M := M)) := h_1836
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1837))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_1864 : (by
                      let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                          intro _raw_i2 h_1836 _
                          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1836)
                          have h_1836 : Litex.In _value_i2 (Litex.R (M := M)) := h_1836
                          exact True.intro);
                        Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                      exact Litex.In _value_i1 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                                  intro _raw_i2 h_1836 _
                                  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1836)
                                  have h_1836 : Litex.In _value_i2 (Litex.R (M := M)) := h_1836
                                  exact True.intro);
                                Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))
                              exact h_1837)
                          )
                      )
                    have h_1865 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.subsetRefl (Litex.R (M := M)))
                          )
                      )
                    have h_1866 : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1865
                          )
                      )
                    have h_1867 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1838
                          )
                      )
                    have h_1868 : Litex.HasFiniteFunctionLimit .left _value_i1 _value_i3 _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1
                          )
                      )
                    have h_1869 : Litex.In _value_i5 (Litex.RPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1840
                          )
                      )
                    have h_1918 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inRPos_positive _value_i5 h_1869)
                          )
                      )
                    have h_1919 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_1918)
                          )
                      )
                    have h_1920 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_1918) _litex_zero.symm)
                          )
                      )
                    exact (show ∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_1921 : Litex.In _value_i11 (Litex.RPos (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_1925 : Litex.In _value_i12 (Litex.R (M := M))) => ((Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i3 _value_i12 (M.real_subset_complex _ h_1867) (M.real_subset_complex _ h_1925))) ∧ (Litex.Lt (Litex.sub _value_i3 _value_i12 (M.real_subset_complex _ h_1867) (M.real_subset_complex _ h_1925)) _value_i11)))) (let _wd_1_0 := _value_i1;
                  let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_2695 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_2695) (M.real_subset_complex _ h_1839));
                  (Litex.abs _wd_2_0 (by
                    let _atomic_wd_1_0 := _wd_2_0
                    exact (Litex.subInR _value_i13 _value_i4 h_2695 h_1839)))) _value_i5));
                  (by
                    have _preimage_target : (by
                    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_3363 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_3363) (M.real_subset_complex _ h_1839));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_2_0 := _wd_2_0
                      exact (Litex.subInR _value_i13 _value_i4 h_3363 h_1839)))) _value_i5))
                    exact Litex.IsSet _atomic_wd_1_0) := (by
                    let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i13 : Litex.Obj (M := M) M.Value) (h_3363 : Litex.In _value_i13 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i13 _value_i4 (M.real_subset_complex _ h_3363) (M.real_subset_complex _ h_1839));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_2_0 := _wd_2_0
                      exact (Litex.subInR _value_i13 _value_i4 h_3363 h_1839)))) _value_i5))
                    exact (Litex.isSet _atomic_wd_1_0))
                    let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_4031 : Litex.In _value_i16 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i16 h_1864 h_4031 True.intro) _wd_1_1))
                    exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame _wd_1_0 _wd_1_0 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_1836 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1836)
                      have h_1836 : Litex.In _value_i2 (Litex.R (M := M)) := h_1836
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_1836 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1836)
                      have h_1836 : Litex.In _value_i2 (Litex.R (M := M)) := h_1836
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_1864))) from (by
                    let _signature := ((let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
                      intro _raw_i2 h_1836 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1836)
                      have h_1836 : Litex.In _value_i2 (Litex.R (M := M)) := h_1836
                      exact True.intro);
                    Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)))).val
                    have _member : Litex.In _value_i1 (Litex.fnSet _signature) := h_1864
                    let _source_domain := (M.standard Litex.StandardSetValue.real)
                    have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
                    have _domain_match : _source_domain = _signature.domain := by
                      apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
                      intro x
                      change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
                      rw [Litex.SetSemantics.sep_members]
                      exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
                    let _domain := Litex.semanticObject _source_domain _domain_set
                    have _control_real_domain : Litex.RealFunctionValue M (Litex.denote _value_i1) := by
                      refine ⟨_signature, _member, ?_, h_1866⟩
                      intro x hx
                      exact h_1865 x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
                    obtain ⟨_limit_threshold, _limit_threshold_member, _limit_control⟩ := Litex.finiteFunctionLimitControl .left _value_i1 _value_i3 _value_i4 _domain _control_real_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_1868 _value_i5 h_1869
                    refine ⟨_limit_threshold, _limit_threshold_member, ?_⟩
                    exact _limit_control
                  ))
                  )
                )
            )
          exact h_1875
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_function_x5f_limit_x5f_left_x5f_control_x5f_by_x5f_theorem_x2f_statement_x2e_lit
