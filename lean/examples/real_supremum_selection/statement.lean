import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_supremum_x5f_selection_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : (by
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
          exact (Litex.realUpperBoundOfForall _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (show ∀ {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 _atomic_wd_1_0), Litex.Le _value_i1 (Litex.number (M := M) (2 : ℂ)) from (by
            intro _Host_i1 _rep_i1 _value_i1 h_19
            have h_20 : Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i1) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_19
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_5 : Litex.Le _value_i1 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.leOfSame (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (h_20).symm (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                  )
              )
            exact h_5
          ))))
      )
  )

theorem h_1595 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i2 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), (∃ (_r _s : ℝ), (Litex.denote _value_i2) = M.number (_r : ℂ) ∧ (M.number (2 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i2 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)) => ((h_1 (M := M))) (Litex.denote _value_i2) _member)
      )
  )

theorem h_1597 : ∃ (_value_i3 : Litex.Obj (M := M) M.Value), ∃ (h_1598 : Litex.In _value_i3 (Litex.R (M := M))), Litex.RealUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) _value_i3 :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i3 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ)))
          have h_1613 : Litex.In _value_i3 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_1614 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) := rfl
          have h_1615 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.RealUpperBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) := (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (h_1 (M := M)))
          exact ⟨_value_i3, h_1613, h_1615⟩
      )
  )

theorem h_1620 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.RealBoundedAbove _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (show ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_1625 : Litex.In _value_i5 (Litex.R (M := M))), Litex.RealUpperBound _atomic_wd_1_0 _value_i5 from (h_1597 (M := M))))
      )
  )

theorem h_1644 : (∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i7))) :=
  (by
    litex_complete =>
      exact (
        (h_1620 (M := M))
      )
  )

theorem h_1649 : ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_1659 : Litex.In _value_i8 (Litex.R (M := M))), (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) _value_i8) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1645 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_1646 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.IsNonempty _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (Litex.insertNonempty _atomic_wd_1_0))
                )
            )
          have h_1647 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.RealBoundedAbove _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (h_1620 (M := M)))
                )
            )
          have h_1657 : (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i10))) :=
            (by
              litex_checked_step =>
                exact (
                  h_1647
                )
            )
          exact (show ∃ (_value_i8 : Litex.Obj (M := M) M.Value), ∃ (h_1658 : Litex.In _value_i8 (Litex.R (M := M))), (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) _value_i8) from (Litex.realSupremumExists (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) h_1645 h_1646 h_1647))
        )
      )
  )

theorem h_1663 : (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (Litex.supremum (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M)))))) (h_1649 (M := M)))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1660 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_1662 : ∃ (_value_i11 : Litex.Obj (M := M) M.Value), ∃ (h_1668 : Litex.In _value_i11 (Litex.R (M := M))), (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) _value_i11) :=
            (by
              litex_checked_step =>
                exact (
                  (h_1649 (M := M))
                )
            )
          exact (show (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          let _atomic_wd_1_1 := (Litex.supremum _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            exact h_1660) h_1662)
          exact (Litex.RealLeastUpperBound _atomic_wd_1_0 _atomic_wd_1_1)) from (Litex.supremumSelected (Litex.supremum (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) h_1660 h_1662)))
        )
      )
  )

theorem h_1682 : (by
  let _atomic_wd_1_0 := (Litex.supremum (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0) (by
    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M)))))) (h_1649 (M := M)))
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.supremum (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M)))))) (h_1649 (M := M)))
          exact (Litex.supremumInR _atomic_wd_1_0))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_supremum_x5f_selection_x2f_statement_x2e_lit
