import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_singleton_x5f_bounds_x2f_statement_x2e_lit

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

theorem h_1596 : (by
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
          exact (Litex.realLowerBoundOfForall _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_1615 : Litex.In _value_i3 _atomic_wd_1_0), Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i3 from (by
            intro _Host_i3 _rep_i3 _value_i3 h_1615
            have h_1616 : Litex.Same _value_i3 (Litex.number (M := M) (2 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have _member : M.mem (Litex.denote _value_i3) (Litex.SetSemantics.insertValue (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.SetSemantics.emptyValue (M := M))) := h_1615
                      exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))
                  )
              )
            have h_1600 : Litex.Le (Litex.number (M := M) (2 : ℂ)) _value_i3 :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      have h_3011 : (by
                        let _atomic_wd_3_1 := _atomic_wd_1_0
                        exact Litex.In (Litex.number (M := M) (2 : ℂ)) _atomic_wd_3_1) :=
                        (by
                          let _atomic_wd_3_1 := _atomic_wd_1_0
                          exact (Litex.inOfSame _value_i3 (Litex.number (M := M) (2 : ℂ)) _atomic_wd_3_1 _atomic_wd_3_1 h_1616 (show @Eq M.Value _ _ from Eq.refl _) h_1615))
                      exact (Litex.leOfSame (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) _value_i3 (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))) (h_1616).symm ((h_1595 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_3011))
                    )
                  )
              )
            exact h_1600
          ))))
      )
  )

theorem h_3053 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i4 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i4 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), (∃ (_r _s : ℝ), (M.number (2 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i4) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i4 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i4 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)) => ((h_1596 (M := M))) (Litex.denote _value_i4) _member)
      )
  )

theorem h_3055 : ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_3056 : Litex.In _value_i5 (Litex.R (M := M))), Litex.RealUpperBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) _value_i5 :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i5 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ)))
          have h_3071 : Litex.In _value_i5 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_3072 : Litex.Same _value_i5 (Litex.number (M := M) (2 : ℂ)) := rfl
          have h_3073 : (by
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
          exact ⟨_value_i5, h_3071, h_3073⟩
      )
  )

theorem h_3079 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_3080 : Litex.In _value_i7 (Litex.R (M := M))), Litex.RealLowerBound (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) _value_i7 :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i7 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.isSet (Litex.number (M := M) (2 : ℂ)))
          have h_3095 : Litex.In _value_i7 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          have h_3096 : Litex.Same _value_i7 (Litex.number (M := M) (2 : ℂ)) := rfl
          have h_3097 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.RealLowerBound _atomic_wd_1_0 (Litex.number (M := M) (2 : ℂ))) := (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (h_1596 (M := M)))
          exact ⟨_value_i7, h_3095, h_3097⟩
      )
  )

theorem h_3102 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.RealBounded _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact ⟨(show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_3109 : Litex.In _value_i9 (Litex.R (M := M))), Litex.RealLowerBound _atomic_wd_1_0 _value_i9 from (h_3079 (M := M))), (show ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_3123 : Litex.In _value_i10 (Litex.R (M := M))), Litex.RealUpperBound _atomic_wd_1_0 _value_i10 from (h_3055 (M := M)))⟩)
      )
  )

theorem h_3142 : (∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i13))) :=
  (by
    litex_complete =>
      exact (
        ((h_3102 (M := M))).1
      )
  )

theorem h_3144 : (∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i14))) :=
  (by
    litex_complete =>
      exact (
        ((h_3102 (M := M))).2
      )
  )

theorem h_3145 : (Litex.RealBoundedAboveValue M (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((h_3102 (M := M))).2
      )
  )

theorem h_3146 : (Litex.RealBoundedBelowValue M (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) :=
  (by
    litex_complete =>
      exact (
        ((h_3102 (M := M))).1
      )
  )

theorem h_3147 : (by
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
          exact (h_3145 (M := M)))
      )
  )

theorem h_3151 : (∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i15))) :=
  (by
    litex_complete =>
      exact (
        (h_3147 (M := M))
      )
  )

theorem h_3152 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.RealBoundedBelow _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (h_3146 (M := M)))
      )
  )

theorem h_3156 : (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i16) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.SetSemantics.insertValue (M.number (2 : ℂ)) (Litex.SetSemantics.emptyValue (M := M))) (Litex.denote _value_i16))) :=
  (by
    litex_complete =>
      exact (
        (h_3152 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_singleton_x5f_bounds_x2f_statement_x2e_lit
