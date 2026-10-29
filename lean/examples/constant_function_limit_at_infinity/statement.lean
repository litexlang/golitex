import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_constant_x5f_function_x5f_limit_x5f_at_x5f_infinity_x2f_statement_x2e_lit

universe u v3 v6 v13
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.number (5 : ℂ))) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M))
  exact (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))))
theorem h_19 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_20 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_23 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_27 : Litex.In _value_i3 (Litex.R (M := M))), ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_28 : Litex.In _value_i4 (Litex.R (M := M))), Litex.Lt _value_i3 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_27
          have h_56 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_27
                )
            )
          let _object_w7 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_56) (Litex.numberInC (M := M) (1 : ℂ)))

          have h_24 : (by
            let _atomic_wd_1_1 := _object_w7
            exact Litex.Lt _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w7
                    exact (Litex.ltAddOfLeOfPos _value_i3 _atomic_wd_1_1 (Litex.leRefl _value_i3 h_56) ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num)))))
                )
            )
          have h_26 : ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_709 : Litex.In _value_i5 (Litex.R (M := M))), Litex.Lt _value_i3 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i5 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote _object_w7) (Litex.isSet _object_w7)
                    have h_755 : Litex.In _value_i5 (Litex.R (M := M)) := (by
                      let _atomic_wd_1_0 := _object_w7
                      exact (Litex.addInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_56 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
                    have h_756 : Litex.Same _value_i5 _object_w7 := rfl
                    have h_757 : (by
                      let _atomic_wd_1_1 := _object_w7
                      exact Litex.Lt _value_i3 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_1 := _object_w7
                      exact h_24)
                    exact ⟨_value_i5, h_755, h_757⟩
                )
            )
          exact (by
            let _real_base := _value_i3
            have _real_base_member : Litex.In _real_base Litex.R := h_56
            obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
            exact ⟨_real_witness, _real_member, _real_order⟩)
        )
      )
  )

theorem h_830 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_845 : Litex.In _value_i6 (Litex.RPos (M := M))), ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_849 : Litex.In _value_i7 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_850 : Litex.In _value_i8 (Litex.R (M := M))) => Litex.Lt _value_i7 _value_i8)) (let _wd_1_0 := (_object_i1 (M := M));
let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_889 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i9 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_889) (Litex.numberInC (M := M) (5 : ℂ)));
(Litex.abs _wd_2_0 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.subInR _value_i9 (Litex.number (M := M) (5 : ℂ)) h_889 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6));
(by
  have _preimage_target : (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_1136 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i9 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_1136) (Litex.numberInC (M := M) (5 : ℂ)));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i9 (Litex.number (M := M) (5 : ℂ)) h_1136 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
  exact Litex.IsSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i9 : Litex.Obj (M := M) M.Value) (h_1136 : Litex.In _value_i9 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i9 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_1136) (Litex.numberInC (M := M) (5 : ℂ)));
  (Litex.abs _wd_2_0 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.subInR _value_i9 (Litex.number (M := M) (5 : ℂ)) h_1136 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
  exact (Litex.isSet _atomic_wd_1_0))
  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i18 : Litex.Obj (M := M) M.Value) (h_1383 : Litex.In _value_i18 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i18 (h_19 (M := M)) h_1383 True.intro) _wd_1_1))
  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_845
          have h_846 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i6 h_845)
                )
            )
          have h_847 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_846)
                )
            )
          have h_848 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_846) _litex_zero.symm)
                )
            )
          have h_1686 : Litex.In _value_i6 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_845
                )
            )
          have h_1687 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i6 h_1686)
                )
            )
          have h_1688 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i6 h_1687)
                )
            )
          have h_1689 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i6 h_1687) _litex_zero.symm)
                )
            )
          have h_834 : ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_1690 : Litex.In _value_i10 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_1691 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.Lt _value_i10 _value_i11)) (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_1730 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_1730) (Litex.numberInC (M := M) (5 : ℂ)));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_1730 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6));
          (by
            have _preimage_target : (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_1977 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_1977) (Litex.numberInC (M := M) (5 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_1977 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
            exact Litex.IsSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_1977 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_1977) (Litex.numberInC (M := M) (5 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_1977 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
            exact (Litex.isSet _atomic_wd_1_0))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i19 : Litex.Obj (M := M) M.Value) (h_2224 : Litex.In _value_i19 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i19 (h_19 (M := M)) h_2224 True.intro) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
            (by
              litex_checked_step =>
                exact (
                  by
                    let _value_i10 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
                    have h_2532 : Litex.In _value_i10 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
                    have h_2533 : Litex.Same _value_i10 (Litex.number (M := M) (0 : ℂ)) := rfl
                    have h_838 : ∀ {_Host_i13 : Type _} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_2549 : Litex.In _value_i13 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_2534 : Litex.In _value_i14 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14))), Litex.In _value_i13 (let _wd_1_0 := (_object_i1 (M := M));
                    let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_2552 : Litex.In _value_i15 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i15 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_2552) (Litex.numberInC (M := M) (5 : ℂ)));
                    (Litex.abs _wd_2_0 (by
                      let _atomic_wd_1_0 := _wd_2_0
                      exact (Litex.subInR _value_i15 (Litex.number (M := M) (5 : ℂ)) h_2552 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6));
                    (by
                      have _preimage_target : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_2886 : Litex.In _value_i15 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i15 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_2886) (Litex.numberInC (M := M) (5 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i15 (Litex.number (M := M) (5 : ℂ)) h_2886 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                      exact Litex.IsSet _atomic_wd_1_0) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_2886 : Litex.In _value_i15 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i15 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_2886) (Litex.numberInC (M := M) (5 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i15 (Litex.number (M := M) (5 : ℂ)) h_2886 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                      exact (Litex.isSet _atomic_wd_1_0))
                      let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i20 : Litex.Obj (M := M) M.Value) (h_3220 : Litex.In _value_i20 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i20 (h_19 (M := M)) h_3220 True.intro) _wd_1_1))
                      exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              intro _Host_i13 _rep_i13 _value_i13 h_2549
                              have h_2550 : (M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_2534 : Litex.In _value_i14 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14)); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_2549)).choose
                                    )
                                )
                              have h_2551 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i13) = M.number (_s : ℂ) ∧ _r < _s) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_2534 : Litex.In _value_i14 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14)); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_2549)).choose_spec
                                    )
                                )
                              have h_3633 : Litex.In _value_i13 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3618 : Litex.In _value_i14 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_2549
                                    )
                                )
                              have h_3634 : (M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3618 : Litex.In _value_i14 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14)); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3633)).choose
                                    )
                                )
                              have h_3635 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i13) = M.number (_s : ℂ) ∧ _r < _s) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      ((let _litex_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i14 : Litex.Obj (M := M) M.Value) (h_3618 : Litex.In _value_i14 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i14)); (Litex.inSetBuilderObj_iff _value_i13 _litex_builder).mp h_3633)).choose_spec
                                    )
                                )
                              have h_839 : Litex.In _value_i13 (Litex.R (M := M)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      h_3634
                                    )
                                )
                              let _object_w40 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i13 (h_19 (M := M)) h_3634 True.intro)

                              have h_840 : (by
                                let _equal_wd_1_0 := _object_w40
                                exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (let _equal_wd_1_0 := _object_w40;
                                      (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i13)) = (M.number (5 : ℂ)) from by
                                        have _litex_residual : (M.number (5 : ℂ)) = (M.number (5 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i13)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i13)) = (M.number (5 : ℂ)) from by
                                        let _litex_original := _equal_wd_1_0
                                        let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                                        let _wd_1_1 := _value_i13;
                                        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_3634 True.intro))
                                        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_20 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                                        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (M.number (5 : ℂ))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                                        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) => (M.number (5 : ℂ))) (Litex.denote _litex_literal.val.argument) = (M.number (5 : ℂ)) from rfl))
                                      ))).trans _litex_residual)))
                                    )
                                )
                              have h_841 : (by
                                let _chain_wd_841_0 := (let _wd_1_0 := (let _wd_2_0 := _object_w40;
                                let _wd_2_1 := (Litex.number (M := M) (5 : ℂ));
                                (Litex.sub _wd_2_0 _wd_2_1 (by
                                  let _atomic_wd_1_0 := _object_w40
                                  exact (Litex.realToComplex _object_w40 (Litex.callInOutput _object_w40))) (Litex.numberInC (M := M) (5 : ℂ))));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.subInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (5 : ℂ)) (by
                                    let _litex_return_call := _object_w40
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))))))
                                exact ((by
                                  let _equal_wd_1_0 := _chain_wd_841_0
                                  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ (Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6)) :=
                                (by
                                  litex_checked_step =>
                                    exact (
                                      (by
                                        let _chain_wd_841_0 := (let _wd_1_0 := (let _wd_2_0 := _object_w40;
                                        let _wd_2_1 := (Litex.number (M := M) (5 : ℂ));
                                        (Litex.sub _wd_2_0 _wd_2_1 (by
                                          let _atomic_wd_1_0 := _object_w40
                                          exact (Litex.realToComplex _object_w40 (Litex.callInOutput _object_w40))) (Litex.numberInC (M := M) (5 : ℂ))));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.subInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (5 : ℂ)) (by
                                            let _litex_return_call := _object_w40
                                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))))))
                                        exact (And.intro (((congrArg (Litex.absValue (M := M)) (congrArg₂ M.subValue h_840 (Litex.sameRefl (Litex.number (M := M) (5 : ℂ)))))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)));
                                        (Litex.abs _wd_1_0 (by
                                          let _atomic_wd_1_0 := _wd_1_0
                                          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) - (5 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) - (5 : ℂ)) (0 : ℝ) (by norm_num))))));
                                        (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) ((|(0 : ℝ)| : ℝ) : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteAbs (_equal_wd_2_0).val.arg (_equal_wd_2_0).wd (0 : ℝ) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((_equal_wd_2_0).val.arg).wd.1 ((_equal_wd_2_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num : ((5 : ℂ) - (5 : ℂ)) = (((0 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))).symm)) h_1687))
                                    )
                                )

                              have h_7120 :=
                                (And.left h_841)

                              have h_7121 :=
                                (And.right h_841)

                              have h_7122 :=
                                h_7120

                              have h_7123 :=
                                h_7121

                              have h_7124 :=
                                (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (let _wd_2_0 := _object_w40;
                                let _wd_2_1 := (Litex.number (M := M) (5 : ℂ));
                                (Litex.sub _wd_2_0 _wd_2_1 (by
                                  let _atomic_wd_1_0 := _object_w40
                                  exact (Litex.realToComplex _object_w40 (Litex.callInOutput _object_w40))) (Litex.numberInC (M := M) (5 : ℂ))));
                                (Litex.abs _wd_1_0 (by
                                  let _atomic_wd_1_0 := _wd_1_0
                                  exact (Litex.subInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (5 : ℂ)) (by
                                    let _litex_return_call := _object_w40
                                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6 _value_i6 (Eq.symm h_7120) (Litex.sameRefl _value_i6) h_7121)
                              exact (by
                                let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                                let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_7125 : Litex.In _value_i15 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i15 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_7125) (Litex.numberInC (M := M) (5 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_2_0 := _wd_2_0
                                  exact (Litex.subInR _value_i15 (Litex.number (M := M) (5 : ℂ)) h_7125 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6));
                                (by
                                  have _preimage_target : (by
                                  let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_7505 : Litex.In _value_i15 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i15 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_7505) (Litex.numberInC (M := M) (5 : ℂ)));
                                  (Litex.abs _wd_2_0 (by
                                    let _atomic_wd_3_0 := _wd_2_0
                                    exact (Litex.subInR _value_i15 (Litex.number (M := M) (5 : ℂ)) h_7505 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                                  exact Litex.IsSet _atomic_wd_2_0) := (by
                                  let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_7505 : Litex.In _value_i15 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i15 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_7505) (Litex.numberInC (M := M) (5 : ℂ)));
                                  (Litex.abs _wd_2_0 (by
                                    let _atomic_wd_3_0 := _wd_2_0
                                    exact (Litex.subInR _value_i15 (Litex.number (M := M) (5 : ℂ)) h_7505 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                                  exact (Litex.isSet _atomic_wd_2_0))
                                  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i21 : Litex.Obj (M := M) M.Value) (h_7885 : Litex.In _value_i21 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i21 (h_19 (M := M)) h_7885 True.intro) _wd_1_1))
                                  exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                                exact (by
                                  let _preimage := _atomic_wd_1_1
                                  let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i22 : Litex.Obj (M := M) M.Value) (h_8360 : Litex.In _value_i22 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _value_i22 (h_19 (M := M)) h_8360 True.intro) (_atomic_wd_1_1).val.target))
                                  have _preimage_same : (Litex.denote _value_i13) = (Litex.denote _value_i13) := rfl
                                  exact (Litex.preimageSetMembers _preimage (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))) (Litex.denote _value_i13)).mpr ⟨Eq.mpr (congrArg (fun x => M.mem x ((Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))).domain) _preimage_same) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) (Litex.denote _value_i13)).mpr ⟨h_3634, True.intro⟩), Eq.mpr (congrArg (fun x => M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _preimage.val.function) x) (Litex.denote _preimage.val.target)) _preimage_same) (by
                                  let _atomic_wd_2_0 := _object_w40
                                  let _atomic_wd_2_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_8809 : Litex.In _value_i15 (Litex.R (M := M))) => Litex.Lt (let _wd_1_0 := (Litex.sub _value_i15 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_8809) (Litex.numberInC (M := M) (5 : ℂ)));
                                  (Litex.abs _wd_1_0 (by
                                    let _atomic_wd_3_0 := _wd_1_0
                                    exact (Litex.subInR _value_i15 (Litex.number (M := M) (5 : ℂ)) h_8809 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                                  exact (by
                                    let _set := _atomic_wd_2_1
                                    exact (Litex.inSetBuilder_iff _atomic_wd_2_0 _set.val.bound _set.val.predicate).mpr ⟨(by
                                    let _atomic_wd_3_0 := _object_w40
                                    exact (by
                                      let _litex_return_call := _object_w40
                                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call))), (by
                                    let _atomic_wd_3_0 := (let _wd_1_0 := (let _wd_2_0 := _object_w40;
                                    let _wd_2_1 := (Litex.number (M := M) (5 : ℂ));
                                    (Litex.sub _wd_2_0 _wd_2_1 (by
                                      let _atomic_wd_1_0 := _object_w40
                                      exact (Litex.realToComplex _object_w40 (Litex.callInOutput _object_w40))) (Litex.numberInC (M := M) (5 : ℂ))));
                                    (Litex.abs _wd_1_0 (by
                                      let _atomic_wd_1_0 := _wd_1_0
                                      exact (Litex.subInR (_atomic_wd_1_0).val.left (Litex.number (M := M) (5 : ℂ)) (by
                                        let _litex_return_call := _object_w40
                                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))))))
                                    exact (Litex.ltOfSame (Litex.number (M := M) (0 : ℂ)) _atomic_wd_3_0 _value_i6 _value_i6 (h_7120).symm (show @Eq M.Value _ _ from Eq.refl _) h_7121))⟩))⟩))
                            )
                          )
                      )
                    have h_844 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_12326 : Litex.In _value_i16 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_12341 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_12341) (Litex.numberInC (M := M) (5 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i17 (Litex.number (M := M) (5 : ℂ)) h_12341 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_12586 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_12586) (Litex.numberInC (M := M) (5 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (5 : ℂ)) h_12586 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_12586 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_12586) (Litex.numberInC (M := M) (5 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i17 (Litex.number (M := M) (5 : ℂ)) h_12586 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i27 : Litex.Obj (M := M) M.Value) (h_12831 : Litex.In _value_i27 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i27 (h_19 (M := M)) h_12831 True.intro) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_12326 : Litex.In _value_i16 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i16))
                              let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                              let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_12341 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_12341) (Litex.numberInC (M := M) (5 : ℂ)));
                              (Litex.abs _wd_2_0 (by
                                let _atomic_wd_2_0 := _wd_2_0
                                exact (Litex.subInR _value_i17 (Litex.number (M := M) (5 : ℂ)) h_12341 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6));
                              (by
                                have _preimage_target : (by
                                let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_12586 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_12586) (Litex.numberInC (M := M) (5 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_3_0 := _wd_2_0
                                  exact (Litex.subInR _value_i17 (Litex.number (M := M) (5 : ℂ)) h_12586 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                                exact Litex.IsSet _atomic_wd_2_0) := (by
                                let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i17 : Litex.Obj (M := M) M.Value) (h_12586 : Litex.In _value_i17 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i17 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_12586) (Litex.numberInC (M := M) (5 : ℂ)));
                                (Litex.abs _wd_2_0 (by
                                  let _atomic_wd_3_0 := _wd_2_0
                                  exact (Litex.subInR _value_i17 (Litex.number (M := M) (5 : ℂ)) h_12586 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                                exact (Litex.isSet _atomic_wd_2_0))
                                let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i27 : Litex.Obj (M := M) M.Value) (h_12831 : Litex.In _value_i27 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i27 (h_19 (M := M)) h_12831 True.intro) _wd_1_1))
                                exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                              exact (Litex.subsetOfForall _atomic_wd_1_0 _atomic_wd_1_1 (by
                                intro _Host_i25 _rep_i25 _value_i25 h_11257
                                have h_11258 : (M.mem (Litex.denote _value_i25) (M.standard Litex.StandardSetValue.real)) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := _atomic_wd_1_0; (Litex.inSetBuilderObj_iff _value_i25 _litex_builder).mp h_11257)).choose
                                      )
                                  )
                                have h_11259 : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i25) = M.number (_s : ℂ) ∧ _r < _s) :=
                                  (by
                                    litex_checked_step =>
                                      exact (
                                        ((let _litex_builder := _atomic_wd_1_0; (Litex.inSetBuilderObj_iff _value_i25 _litex_builder).mp h_11257)).choose_spec
                                      )
                                  )
                                exact (h_838 _value_i25 h_11257)
                              )))
                          )
                      )
                    have h_13937 : (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_13940 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_13955 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_13955) (Litex.numberInC (M := M) (5 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_13955 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_14204 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_14204) (Litex.numberInC (M := M) (5 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_14204 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_14204 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_14204) (Litex.numberInC (M := M) (5 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_14204 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i29 : Litex.Obj (M := M) M.Value) (h_14453 : Litex.In _value_i29 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i29 (h_19 (M := M)) h_14453 True.intro) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) := (by
                      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i11 : Litex.Obj (M := M) M.Value) (h_13940 : Litex.In _value_i11 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11))
                      let _atomic_wd_1_1 := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_13955 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_13955) (Litex.numberInC (M := M) (5 : ℂ)));
                      (Litex.abs _wd_2_0 (by
                        let _atomic_wd_2_0 := _wd_2_0
                        exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_13955 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6));
                      (by
                        have _preimage_target : (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_14204 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_14204) (Litex.numberInC (M := M) (5 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_14204 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                        exact Litex.IsSet _atomic_wd_2_0) := (by
                        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i12 : Litex.Obj (M := M) M.Value) (h_14204 : Litex.In _value_i12 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i12 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_14204) (Litex.numberInC (M := M) (5 : ℂ)));
                        (Litex.abs _wd_2_0 (by
                          let _atomic_wd_3_0 := _wd_2_0
                          exact (Litex.subInR _value_i12 (Litex.number (M := M) (5 : ℂ)) h_14204 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i6))
                        exact (Litex.isSet _atomic_wd_2_0))
                        let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i29 : Litex.Obj (M := M) M.Value) (h_14453 : Litex.In _value_i29 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i29 (h_19 (M := M)) h_14453 True.intro) _wd_1_1))
                        exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))))
                      exact (Litex.subsetOfSame _atomic_wd_1_0 _atomic_wd_1_1 _atomic_wd_1_0 _atomic_wd_1_1 (by
                        let _left := _atomic_wd_1_0
                        let _right := _atomic_wd_1_0
                        exact (show Litex.Same _left _right from rfl)) (by
                        let _left := _atomic_wd_1_1
                        let _right := _atomic_wd_1_1
                        exact (show Litex.Same _left _right from rfl)) h_844))
                    exact ⟨_value_i10, h_2532, h_13937⟩
                )
            )
          exact h_834
        )
      )
  )

theorem h_16439 : (by
  have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
    let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
    have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
    have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
    have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
    refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
    intro x hx
    exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
  )
  have h_17333 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
  exact Litex.HasInfiniteFunctionLimit .positive (_object_i1 (M := M)) (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _function_limit_domain : Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) := (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
            let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
            have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
            have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
            have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
            refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
            intro x hx
            exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
          )
          have h_17333 : Litex.In (Litex.number (M := M) (5 : ℂ)) (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num))
          exact (by
            let _signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
            have _member : Litex.In (_object_i1 (M := M)) (Litex.fnSet _signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
            let _source_domain := (M.standard Litex.StandardSetValue.real)
            have _domain_set : M.isSet _source_domain := (Litex.isSet (Litex.R (M := M)))
            have _domain_match : _source_domain = _signature.domain := by
              apply Litex.SetSemantics.ext _ _ _domain_set _signature.domain_isSet
              intro x
              change M.mem x (Litex.denote (Litex.R (M := M))) ↔ M.mem x (Litex.SetSemantics.sepValue (Litex.denote (Litex.R (M := M))) (fun _ => True))
              rw [Litex.SetSemantics.sep_members]
              exact ⟨fun hx => ⟨hx, True.intro⟩, And.left⟩
            let _domain := Litex.semanticObject _source_domain _domain_set
            exact Litex.infiniteFunctionLimitOfForall .positive (_object_i1 (M := M)) (Litex.number (M := M) (5 : ℂ)) _domain _function_limit_domain (_domain_match.trans (Litex.FunctionSemantics.domainValue_eq _signature.domain_isSet _member).symm) h_17333 (show ∀ {_Host_i32 : Type _} [_rep_i32 : Litex.Representation M _Host_i32] (_value_i32 : Litex.Obj (M := M) _Host_i32) (h_16457 : Litex.In _value_i32 (Litex.R (M := M))), ∃ (_value_i33 : Litex.Obj (M := M) M.Value), ∃ (h_16458 : Litex.In _value_i33 (Litex.R (M := M))), Litex.Lt _value_i32 _value_i33 from (by
            intro _Host_i32 _rep_i32 _value_i32 h_16457
            exact ((h_23 (M := M)) _value_i32 h_16457)
          )) (show ∀ {_Host_i34 : Type _} [_rep_i34 : Litex.Representation M _Host_i34] (_value_i34 : Litex.Obj (M := M) _Host_i34) (h_16490 : Litex.In _value_i34 (Litex.RPos (M := M))), ∃ (_value_i35 : Litex.Obj (M := M) M.Value), ∃ (h_16494 : Litex.In _value_i35 (Litex.R (M := M))), Litex.Subset (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i36 : Litex.Obj (M := M) M.Value) (h_16495 : Litex.In _value_i36 (Litex.R (M := M))) => Litex.Lt _value_i35 _value_i36)) (let _wd_1_0 := (_object_i1 (M := M));
          let _wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_16534 : Litex.In _value_i37 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i37 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_16534) (Litex.numberInC (M := M) (5 : ℂ)));
          (Litex.abs _wd_2_0 (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.subInR _value_i37 (Litex.number (M := M) (5 : ℂ)) h_16534 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i34));
          (by
            have _preimage_target : (by
            let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_16781 : Litex.In _value_i37 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i37 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_16781) (Litex.numberInC (M := M) (5 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_3_0 := _wd_2_0
              exact (Litex.subInR _value_i37 (Litex.number (M := M) (5 : ℂ)) h_16781 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i34))
            exact Litex.IsSet _atomic_wd_2_0) := (by
            let _atomic_wd_2_0 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i37 : Litex.Obj (M := M) M.Value) (h_16781 : Litex.In _value_i37 (Litex.R (M := M))) => Litex.Lt (let _wd_2_0 := (Litex.sub _value_i37 (Litex.number (M := M) (5 : ℂ)) (M.real_subset_complex _ h_16781) (Litex.numberInC (M := M) (5 : ℂ)));
            (Litex.abs _wd_2_0 (by
              let _atomic_wd_3_0 := _wd_2_0
              exact (Litex.subInR _value_i37 (Litex.number (M := M) (5 : ℂ)) h_16781 (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))))) _value_i34))
            exact (Litex.isSet _atomic_wd_2_0))
            let _preimage_builder := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i38 : Litex.Obj (M := M) M.Value) (h_17028 : Litex.In _value_i38 (Litex.R (M := M))) => Litex.In (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True) _wd_1_0 _value_i38 (h_19 (M := M)) h_17028 True.intro) _wd_1_1))
            exact Litex.preimageSet _wd_1_0 _wd_1_1 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True)) (Litex.inOfSame (_object_i1 (M := M)) _wd_1_0 (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M)))))) from (by
            intro _Host_i34 _rep_i34 _value_i34 h_16490
            have h_16491 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i34 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inRPos_positive _value_i34 h_16490)
                  )
              )
            have h_16492 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i34 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i34 h_16491)
                  )
              )
            have h_16493 : ¬ Litex.Same _value_i34 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i34 h_16491) _litex_zero.symm)
                  )
              )
            exact ((h_830 (M := M)) _value_i34 h_16490)
          ))
          ))
      )
  )

noncomputable def _object_w127 := (let _function := (_object_i1 (M := M)); Litex.infiniteFunctionLimit .positive _function (show Litex.RealFunctionValue M (Litex.denote (_object_i1 (M := M))) from by
  let _limit_signature := (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))
  have _limit_function : Litex.In (_object_i1 (M := M)) (Litex.fnSet _limit_signature) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) (Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => True))) ((h_20 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  have _limit_input : Litex.Subset (Litex.R (M := M)) (Litex.R (M := M)) := (Litex.subsetRefl (Litex.R (M := M)))
  have _limit_output : ∀ y, M.mem y _limit_signature.output → M.mem y (Litex.denote (Litex.R (M := M))) := (Litex.subsetRefl (Litex.R (M := M)))
  refine ⟨_limit_signature, _limit_function, ?_, _limit_output⟩
  intro x hx
  exact _limit_input x ((Litex.SetSemantics.sep_members _ _ _).mp hx).1
) (Litex.infiniteFunctionConvergentOfCandidate .positive _function (Litex.number (M := M) (5 : ℂ)) (h_16439 (M := M))))

theorem h_17341 : (by
  let _equal_wd_1_0 := (_object_w127 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w127 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from ((Litex.infiniteFunctionLimitEqCandidate _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (h_16439 (M := M))).trans (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_constant_x5f_function_x5f_limit_x5f_at_x5f_infinity_x2f_statement_x2e_lit
