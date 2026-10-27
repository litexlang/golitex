import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_set_x5f_bound_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3 v15 v16 v17
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_8 : Litex.In _value_i3 _value_i1) (h_1 : Litex.Subset _value_i1 (Litex.R (M := M))) (h_2 : Litex.RealUpperBound _value_i1 _value_i2), Litex.Le _value_i3 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7 _Host_i3 _rep_i3 _value_i3 h_8 h_1 h_2
          have h_23 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i6 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i6 _value_i1), (∃ (_r _s : ℝ), (Litex.denote _value_i6) = M.number (_r : ℂ) ∧ (Litex.denote _value_i2) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i6 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i6 _value_i1) => (h_2) (Litex.denote _value_i6) _member)
                )
            )
          have h_62 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_63 : Litex.In _value_i2 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_64 : Litex.In _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_79 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i8 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i8 _value_i1), (∃ (_r _s : ℝ), (Litex.denote _value_i8) = M.number (_r : ℂ) ∧ (Litex.denote _value_i2) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i8 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i8 _value_i1) => (h_2) (Litex.denote _value_i8) _member)
                )
            )
          have h_5 : Litex.Le _value_i3 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_771 : Litex.In _value_i3 _value_i1 :=
                      h_64
                    exact (Litex.leOfSame _value_i3 _value_i3 _value_i2 _value_i2 (Litex.sameRefl _value_i3) (Litex.sameRefl _value_i2) (h_79 _value_i3 h_771))
                  )
                )
            )
          exact h_5
        )
      )
  )

theorem h_880 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.RealUpperBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.realUpperBoundOfForall _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (show ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_898 : Litex.In _value_i11 _atomic_wd_1_0), Litex.Le _value_i11 (Litex.number (M := M) (2 : ℂ)) from (by
            intro _Host_i11 _rep_i11 _value_i11 h_898
            have h_899 : Litex.Same _value_i11 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i11) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_898
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_884 : Litex.Le _value_i11 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.leOfSame (Litex.number (M := M) (2 : ℂ)) _value_i11 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_899).symm (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                  )
              )
            exact h_884
          ))))
      )
  )

theorem h_2513 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i12 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i12 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), (∃ (_r _s : ℝ), (Litex.denote _value_i12) = M.number (_r : ℂ) ∧ (M.number (2 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i12 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i12 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)) => ((h_880 (M := M))) (Litex.denote _value_i12) _member)
      )
  )

theorem h_2519 : Litex.Le (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_2514 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          have h_2515 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_2516 : (by
            let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (by
                      let _set := _atomic_wd_1_1
                      exact ((Litex.inInsert_iff (Litex.number (M := M) (2 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
                )
            )
          have h_2530 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_2516
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_2517 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (by
                      let _set := _atomic_wd_1_0
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd h_2515 (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_2518 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.RealUpperBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (h_880 (M := M)))
                )
            )
          have h_2544 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i14 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i14 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), (∃ (_r _s : ℝ), (Litex.denote _value_i14) = M.number (_r : ℂ) ∧ (M.number (2 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i14 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i14 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0)) => (h_2518) (Litex.denote _value_i14) _member)
                )
            )
          exact ((h_4 (M := M)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) h_2514 (Litex.number (M := M) (2 : ℂ)) h_2515 (Litex.number (M := M) (2 : ℂ)) h_2516 h_2517 h_2518)
        )
      )
  )

theorem h_2557 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.weakIntegerLowerBoundInN (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (h_2519 (M := M)))
      )
  )

theorem h_2567 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_2584 : Litex.IsSet _value_i15) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_2585 : Litex.In _value_i16 (Litex.R (M := M))) {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_2586 : Litex.In _value_i17 _value_i15) (h_2564 : Litex.Subset _value_i15 (Litex.R (M := M))) (h_2565 : Litex.RealLowerBound _value_i15 _value_i16), Litex.Le _value_i16 _value_i17 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_2584 _Host_i16 _rep_i16 _value_i16 h_2585 _Host_i17 _rep_i17 _value_i17 h_2586 h_2564 h_2565
          have h_2601 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i19 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i19 _value_i15), (∃ (_r _s : ℝ), (Litex.denote _value_i16) = M.number (_r : ℂ) ∧ (Litex.denote _value_i19) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i19 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i19 _value_i15) => (h_2565) (Litex.denote _value_i19) _member)
                )
            )
          have h_2566 : Litex.Le _value_i16 _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_3454 : Litex.In _value_i17 _value_i15 :=
                      h_2586
                    exact (Litex.leOfSame _value_i16 _value_i16 _value_i17 _value_i17 (Litex.sameRefl _value_i16) (Litex.sameRefl _value_i17) (h_2601 _value_i17 h_3454))
                  )
                )
            )
          exact h_2566
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_set_x5f_bound_x5f_theorem_x2f_statement_x2e_lit
