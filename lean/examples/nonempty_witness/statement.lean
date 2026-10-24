import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_witness_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_31 : Litex.IsNonempty (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_2 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
                )
            )
          exact ⟨Litex.denote (Litex.number (M := M) (1 : ℂ)), (by
            let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_15 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1))
            exact (by
              let _set := _atomic_wd_1_1
              exact (Litex.inSetBuilder_iff (Litex.number (M := M) (1 : ℂ)) _set.val.bound _set.val.predicate).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), h_2⟩))⟩
        )
      )
  )

noncomputable def _object_w9 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_34 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2))

theorem h_33 : (by
  let _atomic_wd_1_0 := (_object_w9 (M := M))
  exact Litex.IsNonempty _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w9 (M := M))
          exact (show ((fun (_known_argument_0 : M.Value) => (∃ _member : M.Value, M.mem _member _known_argument_0)) (Litex.denote _atomic_wd_1_0)) from by
            have _known_citation : ((fun (_known_argument_0 : M.Value) => (∃ _member : M.Value, M.mem _member _known_argument_0)) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)))) := (h_31 (M := M))
            exact Eq.mp (((Eq.refl ((fun (_known_argument_0 : M.Value) => (∃ _member : M.Value, M.mem _member _known_argument_0)) (Litex.denote (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) => (∃ _member : M.Value, M.mem _member _known_argument_0)) _known_value)) (show Litex.Same (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i1 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i1 (Litex.R (M := M))) => Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1)) _atomic_wd_1_0 from rfl))) _known_citation
          ))
      )
  )

theorem h_46 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_48 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _atomic_wd_1_0 := (let _setElement_0 := _value_i3;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.IsNonempty _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_48
          have h_51 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_48
                )
            )
          have h_68 : Litex.IsNonempty (let _setElement_0 := _value_i3;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _object_w12 := (let _setElement_0 := _value_i3;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)

                    have h_47 : (by
                      let _atomic_wd_1_1 := _object_w12
                      exact Litex.In _value_i3 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := _object_w12
                              exact (by
                                let _set := _atomic_wd_1_1
                                exact ((Litex.inInsert_iff _value_i3 _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
                          )
                      )
                    exact ⟨Litex.denote _value_i3, (by
                      let _atomic_wd_1_1 := _object_w12
                      exact h_47)⟩
                  )
                )
            )
          exact (by
            let _atomic_wd_1_0 := (let _setElement_0 := _value_i3;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact h_68)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonempty_x5f_witness_x2f_statement_x2e_lit
