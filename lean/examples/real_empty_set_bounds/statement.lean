import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_empty_x5f_set_x5f_bounds_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact Litex.RealUpperBound _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (Litex.realUpperBoundOfForall _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (show ∀ {_Host_i1 : Type _} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.In _value_i1 _atomic_wd_1_0), Litex.Le _value_i1 (Litex.number (M := M) (0 : ℂ)) from (by
            have h_6 : (by
            let _equal_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            let _equal_wd_1_1 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
            intro _Host_i1 _rep_i1 _value_i1 h_8

            exact False.elim (Litex.notInEmpty _value_i1 (Litex.inOfSame _value_i1 _value_i1 _atomic_wd_1_0 (Litex.emptySet (M := M)) (Litex.sameRefl _value_i1) h_6 h_8))))))
      )
  )

theorem h_375 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i2 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i2 (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0)), (∃ (_r _s : ℝ), (Litex.denote _value_i2) = M.number (_r : ℂ) ∧ (M.number (0 : ℂ)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i2 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i2 (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0)) => ((h_1 (M := M))) (Litex.denote _value_i2) _member)
      )
  )

theorem h_376 : (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact Litex.RealLowerBound _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (Litex.realLowerBoundOfForall _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_384 : Litex.In _value_i3 _atomic_wd_1_0), Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 from (by
            have h_382 : (by
            let _equal_wd_1_0 := _atomic_wd_1_0
            let _equal_wd_1_1 := _equal_wd_1_0
            exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) := (show @Eq M.Value _ _ from Eq.refl _)
            intro _Host_i3 _rep_i3 _value_i3 h_384

            exact False.elim (Litex.notInEmpty _value_i3 (Litex.inOfSame _value_i3 _value_i3 _atomic_wd_1_0 (Litex.emptySet (M := M)) (Litex.sameRefl _value_i3) h_382 h_384))))))
      )
  )

theorem h_751 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i4 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i4 (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0)), (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i4) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i4 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i4 (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0)) => ((h_376 (M := M))) (Litex.denote _value_i4) _member)
      )
  )

theorem h_753 : ∃ (_value_i5 : Litex.Obj (M := M) M.Value), ∃ (h_754 : Litex.In _value_i5 (Litex.R (M := M))), Litex.RealUpperBound (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0) _value_i5 :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i5 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
          have h_766 : Litex.In _value_i5 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          have h_767 : Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) := rfl
          have h_768 : (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact Litex.RealUpperBound _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (h_1 (M := M)))
          exact ⟨_value_i5, h_766, h_768⟩
      )
  )

theorem h_774 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_775 : Litex.In _value_i7 (Litex.R (M := M))), Litex.RealLowerBound (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0) _value_i7 :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i7 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
          have h_787 : Litex.In _value_i7 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          have h_788 : Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) := rfl
          have h_789 : (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact Litex.RealLowerBound _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
              _setTail_0)
            exact (h_376 (M := M)))
          exact ⟨_value_i7, h_787, h_789⟩
      )
  )

theorem h_794 : (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact Litex.RealBounded _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact ⟨(show ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_800 : Litex.In _value_i9 (Litex.R (M := M))), Litex.RealLowerBound _atomic_wd_1_0 _value_i9 from (h_774 (M := M))), (show ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_811 : Litex.In _value_i10 (Litex.R (M := M))), Litex.RealUpperBound _atomic_wd_1_0 _value_i10 from (h_753 (M := M)))⟩)
      )
  )

theorem h_825 : (∃ (_value_i13 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i13) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i13))) :=
  (by
    litex_complete =>
      exact (
        ((h_794 (M := M))).1
      )
  )

theorem h_827 : (∃ (_value_i14 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i14) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i14))) :=
  (by
    litex_complete =>
      exact (
        ((h_794 (M := M))).2
      )
  )

theorem h_828 : (Litex.RealBoundedAboveValue M (Litex.SetSemantics.emptyValue (M := M))) :=
  (by
    litex_complete =>
      exact (
        ((h_794 (M := M))).2
      )
  )

theorem h_829 : (Litex.RealBoundedBelowValue M (Litex.SetSemantics.emptyValue (M := M))) :=
  (by
    litex_complete =>
      exact (
        ((h_794 (M := M))).1
      )
  )

theorem h_830 : (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact Litex.RealBoundedAbove _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (h_828 (M := M)))
      )
  )

theorem h_834 : (∃ (_value_i15 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i15) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i15))) :=
  (by
    litex_complete =>
      exact (
        (h_830 (M := M))
      )
  )

theorem h_835 : (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact Litex.RealBoundedBelow _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (h_829 (M := M)))
      )
  )

theorem h_839 : (∃ (_value_i16 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i16) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.SetSemantics.emptyValue (M := M)) (Litex.denote _value_i16))) :=
  (by
    litex_complete =>
      exact (
        (h_835 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_empty_x5f_set_x5f_bounds_x2f_statement_x2e_lit
