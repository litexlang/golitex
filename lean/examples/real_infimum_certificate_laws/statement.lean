import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_infimum_x5f_certificate_x5f_laws_x2f_statement_x2e_lit

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
  exact Litex.RealLowerBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.realLowerBoundOfForall _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (show ∀ {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 _atomic_wd_1_0), Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i1 from (by
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
            have h_5 : Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i1 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.leOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (h_20).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
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

theorem h_1461 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i2 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), (∃ (_r _s : ℝ), (M.number (2 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i2) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
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

theorem h_1471 : (Litex.RealGreatestLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1462 : (by
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
          have h_1463 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_1464 : (by
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
          have h_1466 : ∀ {_Host_i3 : Type u} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_1478 : Litex.In _value_i3 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i3 _rep_i3 _value_i3 h_1478
                    have h_1479 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have _member : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_1478
                              exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                          )
                      )
                    exact ((h_1461 (M := M)) _value_i3 h_1478)
                  )
                )
            )
          have h_1470 : ∀ {_Host_i4 : Type u} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_1510 : Litex.In _value_i4 (Litex.R (M := M))) (h_1468 : ∀ {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1511 : Litex.In _value_i5 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Le _value_i4 _value_i5), Litex.Le _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i4 _rep_i4 _value_i4 h_1510 h_1468
                    have h_1469 : Litex.Le _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have h_1937 : (by
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
                              exact (Litex.leOfSame _value_i4 _value_i4 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.sameRefl _value_i4) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (h_1468 (Litex.number (M := M) (2 : ℂ)) h_1937))
                            )
                          )
                      )
                    exact h_1469
                  )
                )
            )
          exact (show (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.RealGreatestLowerBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)))) from (Litex.realGreatestLowerBoundFromDefinition (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (Litex.number (M := M) (2 : ℂ)) h_1462 h_1463 h_1464 h_1466 (by intro _Host _rep c hc bound; exact h_1470 c hc (by intro _X _rx x hx; exact bound (Litex.denote x) hx))))
        )
      )
  )

noncomputable def _object_w6 := (Litex.infimum (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
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
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M)))))) (Litex.realInfimumExistsOfCertificate (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (Litex.number (M := M) (2 : ℂ)) (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (h_1471 (M := M)))))

theorem h_1987 : (by
  let _equal_wd_1_0 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (Litex.infimumValue_eq_certificate (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (Litex.number (M := M) (2 : ℂ)) (h_1471 (M := M))) (show @Eq M.Value _ _ from Eq.refl _))
      )
  )

theorem h_2007 : ∀ (_value_i7 : Litex.Obj (M := M) M.Value) (h_2036 : Litex.In _value_i7 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i7 :=
  (by
    litex_complete =>
      exact (
        (by
          have h_2003 : (by
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
          have h_2004 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_2005 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealGreatestLowerBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (h_1471 (M := M)))
                )
            )
          exact (show ∀ {_Host_i7 : Type _} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_2016 : Litex.In _value_i7 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i7 from (by intro _Host _rep x hx; exact ((Litex.realGreatestLowerBoundLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (Litex.number (M := M) (2 : ℂ)) h_2003 h_2004 h_2005) (Litex.denote x) hx)))
        )
      )
  )

theorem h_2406 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.RealLowerBound _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (Litex.realLowerBoundOfForall _atomic_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (show ∀ {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_2428 : Litex.In _value_i9 _atomic_wd_1_0), Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 from (by
            intro _Host_i9 _rep_i9 _value_i9 h_2428
            have h_2429 : Litex.Same _value_i9 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i9) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_2428
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_2412 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) _value_i9 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (h_2429).symm ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).mpr (by
                      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) = (2 : ℝ) := by
                        apply Complex.ofReal_injective
                        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))))
                      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
                  )
              )
            exact h_2412
          ))))
      )
  )

theorem h_3877 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i10 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i10 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), (∃ (_r _s : ℝ), (M.number (1 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i10) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i10 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i10 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)) => ((h_2406 (M := M))) (Litex.denote _value_i10) _member)
      )
  )

theorem h_3884 : ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_3937 : Litex.In _value_i12 (Litex.R (M := M))), (Litex.RealGreatestLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) _value_i12) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_3878 : (by
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
          have h_3879 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_3880 : (by
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
          have h_3882 : ∀ {_Host_i11 : Type u} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_3893 : Litex.In _value_i11 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i11 _rep_i11 _value_i11 h_3893
                    have h_3894 : Litex.Same _value_i11 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have _member : M.mem (Litex.denote _value_i11) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_3893
                              exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                          )
                      )
                    exact ((h_3877 (M := M)) _value_i11 h_3893)
                  )
                )
            )
          exact (show ∃ (_value_i12 : Litex.Obj (M := M) M.Value), ∃ (h_3934 : Litex.In _value_i12 (Litex.R (M := M))), (Litex.RealGreatestLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) _value_i12) from (Litex.realGreatestLowerBoundExists (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (Litex.number (M := M) (1 : ℂ)) h_3878 h_3879 h_3880 h_3882))
        )
      )
  )

noncomputable def _value_i15 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_3942 : Litex.In _value_i14 (Litex.R (M := M))), (Litex.RealGreatestLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) _value_i14) from (h_3884 (M := M))))

theorem h_3945 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_3942 : Litex.In _value_i14 (Litex.R (M := M))), (Litex.RealGreatestLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) _value_i14) from (h_3884 (M := M)))))))
      )
  )

theorem h_3946 : (Litex.RealGreatestLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (_value_i15 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (h_3942 : Litex.In _value_i14 (Litex.R (M := M))), (Litex.RealGreatestLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) _value_i14) from (h_3884 (M := M)))))))
      )
  )

theorem h_3952 : Litex.Same (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_3947 : (by
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
          have h_3948 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_3945 (M := M))
                )
            )
          have h_3949 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealGreatestLowerBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (h_3946 (M := M)))
                )
            )
          have h_3950 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
                )
            )
          have h_3951 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealGreatestLowerBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (h_1471 (M := M)))
                )
            )
          exact (show Litex.Same (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) from (Litex.realGreatestLowerBoundUnique (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_3947 h_3948 h_3949 h_3950 h_3951))
        )
      )
  )

theorem h_3983 : Litex.Same (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_3952 (M := M))
      )
  )

theorem h_3989 : Litex.Le (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_3985 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.inOfSame (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_3952 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3945 (M := M))) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_3986 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_3945 (M := M))
                )
            )
          have h_3987 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealGreatestLowerBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (_value_i15 (M := M)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (h_1471 (M := M))
                      exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) _known_value)) ((h_3952 (M := M))).symm)) _known_citation
                    ))
                )
            )
          have h_3988 : (by
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
          have h_4025 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_3988
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          exact (show Litex.Le (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) from (Litex.realGreatestLowerBoundMember (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_3985 h_3986 h_3987 h_3988))
        )
      )
  )

theorem h_4080 : Litex.Le (Litex.number (M := M) (1 : ℂ)) (_value_i15 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4074 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.inOfSame (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_3952 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3945 (M := M))) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_4075 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_3945 (M := M))
                )
            )
          have h_4076 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealGreatestLowerBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (_value_i15 (M := M)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (h_1471 (M := M))
                      exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) _known_value)) ((h_3952 (M := M))).symm)) _known_citation
                    ))
                )
            )
          have h_4077 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_4079 : ∀ {_Host_i18 : Type u} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_4105 : Litex.In _value_i18 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)), Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i18 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i18 _rep_i18 _value_i18 h_4105
                    have h_4106 : Litex.Same _value_i18 (Litex.number (M := M) (2 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              have _member : M.mem (Litex.denote _value_i18) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_4105
                              exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                          )
                      )
                    exact ((h_3877 (M := M)) _value_i18 h_4105)
                  )
                )
            )
          exact (show Litex.Le (Litex.number (M := M) (1 : ℂ)) (_value_i15 (M := M)) from (Litex.realGreatestLowerBoundCompareBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (_value_i15 (M := M)) (Litex.number (M := M) (1 : ℂ)) h_4074 h_4075 h_4076 h_4077 h_4079))
        )
      )
  )

theorem h_4184 : ∃ (_value_i20 : Litex.Obj (M := M) M.Value), ∃ (h_4275 : Litex.In _value_i20 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Lt _value_i20 (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4178 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.inOfSame (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_3952 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_3945 (M := M))) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_4179 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_3945 (M := M))
                )
            )
          have h_4180 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealGreatestLowerBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (_value_i15 (M := M)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (h_1471 (M := M))
                      exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) _known_value)) ((h_3952 (M := M))).symm)) _known_citation
                    ))
                )
            )
          have h_4181 : Litex.In (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))
                )
            )
          have h_4182 : Litex.Lt (_value_i15 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (h_3989 (M := M)) (Litex.NativeBridge.ltOfDenoteReal (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℝ) (3 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num)))
                )
            )
          exact (show ∃ (_value_i20 : Litex.Obj (M := M) M.Value), ∃ (h_4244 : Litex.In _value_i20 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), Litex.Lt _value_i20 (Litex.number (M := M) (3 : ℂ)) from (Litex.realGreatestLowerBoundCrosses (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) (_value_i15 (M := M)) (Litex.number (M := M) (3 : ℂ)) h_4178 h_4179 h_4180 h_4181 h_4182))
        )
      )
  )

noncomputable def _value_i23 : Litex.Obj (M := M) M.Value :=
  Classical.choose ((show ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_4316 : Litex.In _value_i22 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), Litex.Lt _value_i22 (Litex.number (M := M) (3 : ℂ)) from (h_4184 (M := M))))

theorem h_4355 : Litex.In (_value_i23 (M := M)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose ((Classical.choose_spec ((show ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_4316 : Litex.In _value_i22 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), Litex.Lt _value_i22 (Litex.number (M := M) (3 : ℂ)) from (h_4184 (M := M)))))))
      )
  )

theorem h_4356 : Litex.Same (_value_i23 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have _member : M.mem (Litex.denote (_value_i23 (M := M))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := (h_4355 (M := M))
          exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
      )
  )

theorem h_4357 : Litex.Lt (_value_i23 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Classical.choose_spec ((Classical.choose_spec ((show ∃ (_value_i22 : Litex.Obj (M := M) M.Value), ∃ (h_4316 : Litex.In _value_i22 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), Litex.Lt _value_i22 (Litex.number (M := M) (3 : ℂ)) from (h_4184 (M := M)))))))
      )
  )

theorem h_4381 : Litex.Lt (_value_i23 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_4357 (M := M))
      )
  )

theorem h_4405 : Litex.Same (_value_i23 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_4356 (M := M))
      )
  )

theorem h_4410 : ∀ {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_4411 : Litex.IsSet _value_i24) {_Host_i25 : Type v25} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (h_4412 : Litex.In _value_i25 (Litex.R (M := M))) {_Host_i26 : Type v26} [_rep_i26 : Litex.Representation M _Host_i26] (_value_i26 : Litex.Obj (M := M) _Host_i26) (h_4413 : Litex.In _value_i26 _value_i24) (h_4407 : Litex.Subset _value_i24 (Litex.R (M := M))) (h_4408 : (Litex.RealGreatestLowerBound _value_i24 _value_i25)), Litex.Le _value_i25 _value_i26 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i24 _rep_i24 _value_i24 h_4411 _Host_i25 _rep_i25 _value_i25 h_4412 _Host_i26 _rep_i26 _value_i26 h_4413 h_4407 h_4408
          have h_4467 : Litex.IsSet _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  h_4411
                )
            )
          have h_4468 : Litex.In _value_i25 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4412
                )
            )
          have h_4469 : Litex.In _value_i26 _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  h_4413
                )
            )
          have h_4479 : Litex.Le _value_i25 _value_i26 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_4475 : Litex.Subset _value_i24 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4407
                          )
                      )
                    have h_4476 : Litex.In _value_i25 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4468
                          )
                      )
                    have h_4477 : (Litex.RealGreatestLowerBound _value_i24 _value_i25) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4408
                          )
                      )
                    have h_4478 : Litex.In _value_i26 _value_i24 :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_4469
                          )
                      )
                    exact (show Litex.Le _value_i25 _value_i26 from (Litex.realGreatestLowerBoundMember _value_i24 _value_i25 _value_i26 h_4475 h_4476 h_4477 h_4478))
                  )
                )
            )
          exact h_4479
        )
      )
  )

theorem h_4744 : Litex.Le (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4745 : (by
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
          have h_4746 : Litex.In (_value_i15 (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_3945 (M := M))
                )
            )
          have h_4747 : (by
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
                    exact (Litex.inOfSame (_value_i23 (M := M)) (Litex.number (M := M) (2 : ℂ)) _atomic_wd_1_1 _atomic_wd_1_1 (h_4356 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_4355 (M := M))))
                )
            )
          have h_4767 : Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have _member : M.mem (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_4747
                    exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                )
            )
          have h_4748 : (by
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
                      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (Litex.inOfSame (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_3952 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_4746) (Litex.emptySubset (Litex.R (M := M))))))
                )
            )
          have h_4749 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (Litex.RealGreatestLowerBound _atomic_wd_1_0 (_value_i15 (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (_value_i15 (M := M)))) from by
                      have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) := (h_1471 (M := M))
                      exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) (Litex.denote (Litex.number (M := M) (2 : ℂ)))))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealGreatestLowerBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _atomic_wd_1_0) _known_value)) ((h_3952 (M := M))).symm)) _known_citation
                    ))
                )
            )
          have h_4750 : Litex.Le (_value_i15 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_4410 (M := M)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_4745 (_value_i15 (M := M)) h_4746 (Litex.number (M := M) (2 : ℂ)) h_4747 h_4748 h_4749)
                )
            )
          exact h_4750
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_infimum_x5f_certificate_x5f_laws_x2f_statement_x2e_lit
