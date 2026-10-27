import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_supremum_x5f_certificate_x5f_laws_x2f_statement_x2e_lit

universe u v24 v25 v26
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

theorem h_1605 : (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1596 : (by
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
          have h_1597 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_1598 : (by
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
          have h_1600 : ∀ {_Host_i3 : Type u} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_1612 : Litex.In _value_i3 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Le _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i3 _rep_i3 _value_i3 h_1612
                    have h_1613 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have _member : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_1612
                              exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                          )
                      )
                    exact ((h_1595 (M := M)) _value_i3 h_1612)
                  )
                )
            )
          have h_1604 : ∀ {_Host_i4 : Type u} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_1644 : Litex.In _value_i4 (Litex.R (M := M))) (h_1602 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1645 : Litex.In _value_i5 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Le _value_i5 _value_i4), Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i4 _rep_i4 _value_i4 h_1644 h_1602
                    have h_1603 : Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i4 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have h_2078 : (by
                                let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                                  let _setTail_1 := Litex.emptySet (M := M);
                                  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                  _setTail_0)
                                exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_2_1) :=
                                (by
                                  let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                                    let _setTail_1 := Litex.emptySet (M := M);
                                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                                    _setTail_0)
                                  exact (by
                                    let _set := _atomic_wd_2_1
                                    exact ((Litex.inInsert_iff (Litex.number (M := M) (2 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
                              exact (Litex.leOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) _value_i4 _value_i4 (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (Litex.sameRefl _value_i4) (h_1602 (Litex.number (M := M) (2 : ℂ)) h_2078))
                            )
                          )
                      )
                    exact h_1603
                  )
                )
            )
          exact (show (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.RealLeastUpperBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)))) from (Litex.realLeastUpperBoundFromDefinition (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (Litex.number (M := M) (2 : ℂ)) h_1596 h_1597 h_1598 h_1600 (by intro _Host _rep c hc bound; exact h_1604 c hc (by intro _X _rx x hx; exact bound (Litex.denote x) hx))))
        )
      )
  )

noncomputable def _object_w6 := (Litex.supremum (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
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
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M)))))) (Litex.realSupremumExistsOfCertificate (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (Litex.number (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (h_1605 (M := M)))))

theorem h_2136 : (by
  let _equal_wd_1_0 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (Litex.supremumValue_eq_certificate (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (Litex.number (M := M) (2 : ℂ)) (h_1605 (M := M))) (show @Eq M.Value _ _ from Eq.refl _))
      )
  )

theorem h_2156 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_2185 : Litex.In _value_i7 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Le _value_i7 (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_2152 : (by
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
          have h_2153 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_2154 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealLeastUpperBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (h_1605 (M := M)))
                )
            )
          exact (show ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_2165 : Litex.In _value_i7 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), Litex.Le _value_i7 (Litex.number (M := M) (2 : ℂ)) from (by intro _Host _rep x hx; exact ((Litex.realLeastUpperBoundUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (Litex.number (M := M) (2 : ℂ)) h_2152 h_2153 h_2154) (Litex.denote x) hx)))
        )
      )
  )

theorem h_2555 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.RealUpperBound _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.realUpperBoundOfForall _atomic_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (show ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_2577 : Litex.In _value_i9 _atomic_wd_1_0), Litex.Le _value_i9 (Litex.number (M := M) (3 : ℂ)) from (by
            intro _Host_i9 _rep_i9 _value_i9 h_2577
            have h_2578 : Litex.Same _value_i9 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i9) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_2577
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_2561 : Litex.Le _value_i9 (Litex.number (M := M) (3 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.leOfSame (Litex.number (M := M) (2 : ℂ)) _value_i9 (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_2578).symm (Litex.sameRefl (Litex.number (M := M) (3 : ℂ))) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) = (3 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                  )
              )
            exact h_2561
          ))))
      )
  )

theorem h_4150 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i10 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i10 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), (∃ (_r _s : ℝ), (Litex.denote _value_i10) = M.number (_r : ℂ) ∧ (M.number (3 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i10 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i10 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)) => ((h_2555 (M := M))) (Litex.denote _value_i10) _member)
      )
  )

theorem h_4157 : ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_4210 : Litex.In _value_i12 (Litex.R (M := M))), (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) _value_i12) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4151 : (by
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
          have h_4152 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
                )
            )
          have h_4153 : (by
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
          have h_4155 : ∀ {_Host_i11 : Type u} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_4166 : Litex.In _value_i11 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Le _value_i11 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i11 _rep_i11 _value_i11 h_4166
                    have h_4167 : Litex.Same _value_i11 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have _member : M.mem (Litex.denote _value_i11) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_4166
                              exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                          )
                      )
                    exact ((h_4150 (M := M)) _value_i11 h_4166)
                  )
                )
            )
          exact (show ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_4207 : Litex.In _value_i12 (Litex.R (M := M))), (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) _value_i12) from (Litex.realLeastUpperBoundExists (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (Litex.number (M := M) (3 : ℂ)) h_4151 h_4152 h_4153 h_4155))
        )
      )
  )

noncomputable def _value_i15 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_4215 : Litex.In _value_i14 (Litex.R (M := M))), (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) _value_i14) from (h_4157 (M := M))))

theorem h_4218 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_4215 : Litex.In _value_i14 (Litex.R (M := M))), (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) _value_i14) from (h_4157 (M := M)))))))
      )
  )

theorem h_4219 : (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (_value_i15 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_4215 : Litex.In _value_i14 (Litex.R (M := M))), (Litex.RealLeastUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) _value_i14) from (h_4157 (M := M)))))))
      )
  )

theorem h_4225 : Litex.Same (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4220 : (by
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
          have h_4221 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_4218 (M := M))
                )
            )
          have h_4222 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealLeastUpperBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (h_4219 (M := M)))
                )
            )
          have h_4223 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_4224 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealLeastUpperBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (h_1605 (M := M)))
                )
            )
          exact (show Litex.Same (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) from (Litex.realLeastUpperBoundUnique (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_4220 h_4221 h_4222 h_4223 h_4224))
        )
      )
  )

theorem h_4256 : Litex.Same (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_4225 (M := M))
      )
  )

theorem h_4262 : Litex.Le (Litex.number (M := M) (2 : ℂ)) (_value_i15 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4258 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.inOfSame (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4225 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_4218 (M := M))) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_4259 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_4218 (M := M))
                )
            )
          have h_4260 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealLeastUpperBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (_value_i15 (M := M)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (h_1605 (M := M))
                      exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) _known_value)) ((h_4225 (M := M))).symm)) _known_citation
                    ))
                )
            )
          have h_4261 : (by
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
          have h_4298 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_4261
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          exact (show Litex.Le (Litex.number (M := M) (2 : ℂ)) (_value_i15 (M := M)) from (Litex.realLeastUpperBoundMember (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_4258 h_4259 h_4260 h_4261))
        )
      )
  )

theorem h_4355 : Litex.Le (_value_i15 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4349 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.inOfSame (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4225 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_4218 (M := M))) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_4350 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_4218 (M := M))
                )
            )
          have h_4351 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealLeastUpperBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (_value_i15 (M := M)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (h_1605 (M := M))
                      exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) _known_value)) ((h_4225 (M := M))).symm)) _known_citation
                    ))
                )
            )
          have h_4352 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
                )
            )
          have h_4354 : ∀ {_Host_i18 : Type u} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_4380 : Litex.In _value_i18 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Le _value_i18 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i18 _rep_i18 _value_i18 h_4380
                    have h_4381 : Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have _member : M.mem (Litex.denote _value_i18) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_4380
                              exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                          )
                      )
                    exact ((h_4150 (M := M)) _value_i18 h_4380)
                  )
                )
            )
          exact (show Litex.Le (_value_i15 (M := M)) (Litex.number (M := M) (3 : ℂ)) from (Litex.realLeastUpperBoundCompareBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (_value_i15 (M := M)) (Litex.number (M := M) (3 : ℂ)) h_4349 h_4350 h_4351 h_4352 h_4354))
        )
      )
  )

theorem h_4462 : ∃ (_value_i20 : Litex.Obj (M := M) M.Value), ∃ (h_4549 : Litex.In _value_i20 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Lt (Litex.number (M := M) (1 : ℂ)) _value_i20 :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4456 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.inOfSame (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4225 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_4218 (M := M))) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_4457 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_4218 (M := M))
                )
            )
          have h_4458 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealLeastUpperBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (_value_i15 (M := M)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (h_1605 (M := M))
                      exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) _known_value)) ((h_4225 (M := M))).symm)) _known_citation
                    ))
                )
            )
          have h_4459 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_4460 : Litex.Lt (Litex.number (M := M) (1 : ℂ)) (_value_i15 (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltLeTrans (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_value_i15 (M := M)) (Litex.NativeBridge.ltOfDenoteReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℝ) (2 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num)) (h_4262 (M := M)))
                )
            )
          have h_4520 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_value_i15 (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_value_i15 (M := M)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_4459).mpr (by
                    have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                    have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) h_4459 = (1 : ℝ) := by
                      apply Complex.ofReal_injective
                      exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) h_4459).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                    exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) h_4460)
                )
            )
          exact (show ∃ (_value_i20 : Litex.Obj (M := M) M.Value), ∃ (h_4521 : Litex.In _value_i20 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), Litex.Lt (Litex.number (M := M) (1 : ℂ)) _value_i20 from (Litex.realLeastUpperBoundCrosses (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (_value_i15 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_4456 h_4457 h_4458 h_4459 h_4460))
        )
      )
  )

noncomputable def _value_i23 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_4583 : Litex.In _value_i22 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Lt (Litex.number (M := M) (1 : ℂ)) _value_i22 from (h_4462 (M := M))))

theorem h_4615 : Litex.In (_value_i23 (M := M)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_4583 : Litex.In _value_i22 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), Litex.Lt (Litex.number (M := M) (1 : ℂ)) _value_i22 from (h_4462 (M := M)))))))
      )
  )

theorem h_4616 : Litex.Same (_value_i23 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (_value_i23 (M := M))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := (h_4615 (M := M))
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

theorem h_4617 : Litex.Lt (Litex.number (M := M) (1 : ℂ)) (_value_i23 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_4583 : Litex.In _value_i22 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), Litex.Lt (Litex.number (M := M) (1 : ℂ)) _value_i22 from (h_4462 (M := M)))))))
      )
  )

theorem h_4633 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_value_i23 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_value_i23 (M := M)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (h_4617 (M := M)))
      )
  )

theorem h_4634 : Litex.Lt (Litex.number (M := M) (1 : ℂ)) (_value_i23 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (h_4617 (M := M))
      )
  )

theorem h_4654 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_value_i23 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_value_i23 (M := M)) ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
          have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
          have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
            apply Complex.ofReal_injective
            exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
          exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))) (h_4634 (M := M)))
      )
  )

theorem h_4655 : Litex.Same (_value_i23 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_4616 (M := M))
      )
  )

theorem h_4660 : ∀ {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_4661 : Litex.IsSet _value_i24) {_Host_i25 : Type v25} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (h_4662 : Litex.In _value_i25 (Litex.R (M := M))) {_Host_i26 : Type v26} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (h_4663 : Litex.In _value_i26 _value_i24) (h_4657 : Litex.Subset _value_i24 (Litex.R (M := M))) (h_4658 : (Litex.RealLeastUpperBound _value_i24 _value_i25)), Litex.Le _value_i26 _value_i25 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i24 _rep_i24 _value_i24 h_4661 _Host_i25 _rep_i25 _value_i25 h_4662 _Host_i26 _rep_i26 _value_i26 h_4663 h_4657 h_4658
          have h_4717 : Litex.IsSet _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  h_4661
                )
            )
          have h_4718 : Litex.In _value_i25 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4662
                )
            )
          have h_4719 : Litex.In _value_i26 _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  h_4663
                )
            )
          have h_4729 : Litex.Le _value_i26 _value_i25 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_4725 : Litex.Subset _value_i24 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4657
                          )
                      )
                    have h_4726 : Litex.In _value_i25 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4718
                          )
                      )
                    have h_4727 : (Litex.RealLeastUpperBound _value_i24 _value_i25) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4658
                          )
                      )
                    have h_4728 : Litex.In _value_i26 _value_i24 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4719
                          )
                      )
                    exact (show Litex.Le _value_i26 _value_i25 from (Litex.realLeastUpperBoundMember _value_i24 _value_i25 _value_i26 h_4725 h_4726 h_4727 h_4728))
                  )
                )
            )
          exact h_4729
        )
      )
  )

theorem h_4994 : Litex.Le (Litex.number (M := M) (2 : ℂ)) (_value_i15 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4995 : (by
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
          have h_4996 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_4218 (M := M))
                )
            )
          have h_4997 : (by
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
                    exact (Litex.inOfSame (_value_i23 (M := M)) (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1 _atomic_wd_1_1 (h_4616 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_4615 (M := M))))
                )
            )
          have h_5017 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_4997
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_4998 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.inOfSame (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_4225 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_4996) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_4999 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealLeastUpperBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (_value_i15 (M := M)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (h_1605 (M := M))
                      exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealLeastUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) _known_value)) ((h_4225 (M := M))).symm)) _known_citation
                    ))
                )
            )
          have h_5000 : Litex.Le (Litex.number (M := M) (2 : ℂ)) (_value_i15 (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_4660 (M := M)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_4995 (_value_i15 (M := M)) h_4996 (Litex.number (M := M) (2 : ℂ)) h_4997 h_4998 h_4999)
                )
            )
          exact h_5000
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_supremum_x5f_certificate_x5f_laws_x2f_statement_x2e_lit
