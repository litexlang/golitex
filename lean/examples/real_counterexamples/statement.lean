import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_counterexamples_x2f_statement_x2e_lit

universe u v3 v5
variable {M : Litex.Semantics.{u}}

theorem h_2 : ¬ (∀ (_value_i1 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)) → (∀ (_value_i2 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)) → (((Litex.denote _value_i1) = (Litex.denote _value_i2))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _universal
          have _counterexample : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_5 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_6 : Litex.In _value_i2 (Litex.R (M := M))), ¬ Litex.Same _value_i1 _value_i2 := (by
          let _real_base := (Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))
          have _real_base_member : Litex.In _real_base Litex.R := (Litex.NativeBridge.numberInR (M := M) 0)
          obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealAbove _real_base _real_base_member
          exact ⟨_real_base, _real_base_member, _real_witness, _real_member, (Litex.ltNotSame _real_base _real_witness _real_order)⟩)
          rcases _counterexample with ⟨_value_i1, h_5, _value_i2, h_6, h_3⟩
          have _positive : ((Litex.denote _value_i1) = (Litex.denote _value_i2)) := _universal _value_i1 h_5 _value_i2 h_6
          have _negative : (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i2))) := h_3
          have _refute : ¬ (((Litex.denote _value_i1) = (Litex.denote _value_i2))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
          exact _refute _positive)
      )
  )

theorem h_8 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_5 : Litex.In _value_i1 (Litex.R (M := M))), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_6 : Litex.In _value_i2 (Litex.R (M := M))), ¬ Litex.Same _value_i1 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          have _counterexample : (∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i1) (M.standard Litex.StandardSetValue.real)), ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i1) = (Litex.denote _value_i2)))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using (h_2 (M := M))
          exact _counterexample)
      )
  )

theorem h_9 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M)))

theorem h_12 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) : ¬ (∀ (_value_i4 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)) → (((Litex.denote _value_i4) = (Litex.denote _value_i3)))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _universal
          have _counterexample : ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_15 : Litex.In _value_i4 (Litex.R (M := M))), ¬ Litex.Same _value_i4 _value_i3 := (by
          let _real_base := _value_i3
          have _real_base_member : Litex.In _real_base Litex.R := h_10
          obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
          exact ⟨_real_witness, _real_member, (Litex.ltNotSame _real_witness _real_base _real_order)⟩)
          rcases _counterexample with ⟨_value_i4, h_15, h_13⟩
          have _positive : ((Litex.denote _value_i4) = (Litex.denote _value_i3)) := _universal _value_i4 h_15
          have _negative : (¬ ((Litex.denote _value_i4) = (Litex.denote _value_i3))) := h_13
          have _refute : ¬ (((Litex.denote _value_i4) = (Litex.denote _value_i3))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
          exact _refute _positive)
      )
  )

theorem h_22 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) : ∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (h_15 : Litex.In _value_i4 (Litex.R (M := M))), ¬ Litex.Same _value_i4 _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          have _counterexample : (∃ (_value_i4 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i4) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i4) = (Litex.denote _value_i3)))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using (h_12 (M := M) (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_10)
          exact _counterexample)
      )
  )

theorem h_25 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_28 : Litex.In _value_i5 (Litex.R (M := M))), ∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (h_29 : Litex.In _value_i6 (Litex.R (M := M))), ¬ Litex.Same _value_i6 _value_i5 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_28
          have h_30 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_28
                )
            )
          have h_27 : ¬ (∀ (_value_i7 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)) → (((Litex.denote _value_i7) = (Litex.denote _value_i5)))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    intro _universal
                    have _counterexample : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_33 : Litex.In _value_i7 (Litex.R (M := M))), ¬ Litex.Same _value_i7 _value_i5 := (by
                    let _real_base := _value_i5
                    have _real_base_member : Litex.In _real_base Litex.R := h_30
                    obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
                    exact ⟨_real_witness, _real_member, (Litex.ltNotSame _real_witness _real_base _real_order)⟩)
                    rcases _counterexample with ⟨_value_i7, h_33, h_31⟩
                    have _positive : ((Litex.denote _value_i7) = (Litex.denote _value_i5)) := _universal _value_i7 h_33
                    have _negative : (¬ ((Litex.denote _value_i7) = (Litex.denote _value_i5))) := h_31
                    have _refute : ¬ (((Litex.denote _value_i7) = (Litex.denote _value_i5))) := by
                      simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
                    exact _refute _positive)
                )
            )

          have h_40 : ∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (h_33 : Litex.In _value_i7 (Litex.R (M := M))), ¬ Litex.Same _value_i7 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    classical
                    have _counterexample : (∃ (_value_i7 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i7) (M.standard Litex.StandardSetValue.real)), (¬ ((Litex.denote _value_i7) = (Litex.denote _value_i5)))) := by
                      simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using h_27
                    exact _counterexample)
                )
            )
          exact (by
            let _real_base := _value_i5
            have _real_base_member : Litex.In _real_base Litex.R := h_30
            obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.existsRealBelow _real_base _real_base_member
            exact ⟨_real_witness, _real_member, (Litex.ltNotSame _real_witness _real_base _real_order)⟩)
        )
      )
  )

theorem h_50 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) : ∃ (_value_i9 : Litex.Obj (M := M) M.Value), ∃ (h_51 : Litex.In _value_i9 (Litex.R (M := M))), ¬ Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i9 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
          have h_65 : Litex.In _value_i9 (Litex.R (M := M)) := (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          have h_66 : Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) := rfl
          have h_67 : ¬ Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) := ((not_congr (Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i9 (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_66 (show @Eq M.Value _ _ from Eq.refl _) h_65) (Litex.inOfSame _value_i9 (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_66 (show @Eq M.Value _ _ from Eq.refl _) h_65))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i9 (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_66 (show @Eq M.Value _ _ from Eq.refl _) h_65) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i9 (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_66 (show @Eq M.Value _ _ from Eq.refl _) h_65)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i9 (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_66 (show @Eq M.Value _ _ from Eq.refl _) h_65) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.inOfSame _value_i9 (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) h_66 (show @Eq M.Value _ _ from Eq.refl _) h_65)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => ¬ (_litex_r < _litex_s)) _litex_right_value _litex_left_value) (by norm_num)))
          exact ⟨_value_i9, h_65, h_67⟩
      )
  )

theorem h_79 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) : ¬ (∀ (_value_i10 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)) → ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i10) = M.number (_s : ℂ) ∧ _r < _s))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _universal
          have _counterexample : ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_82 : Litex.In _value_i10 (Litex.R (M := M))), ¬ Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 := (h_50 (M := M) (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_10)
          rcases _counterexample with ⟨_value_i10, h_82, h_80⟩
          have _positive : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i10) = M.number (_s : ℂ) ∧ _r < _s) := _universal _value_i10 h_82
          have _negative : (¬ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i10) = M.number (_s : ℂ) ∧ _r < _s))) := h_80
          have _refute : ¬ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i10) = M.number (_s : ℂ) ∧ _r < _s)) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
          exact _refute _positive)
      )
  )

theorem h_94 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_10 : Litex.In _value_i3 (Litex.R (M := M))) : ∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (h_82 : Litex.In _value_i10 (Litex.R (M := M))), ¬ Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i10 :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          have _counterexample : (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)), (¬ ((∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (Litex.denote _value_i10) = M.number (_s : ℂ) ∧ _r < _s)))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using (h_79 (M := M) (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_10)
          exact _counterexample)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_counterexamples_x2f_statement_x2e_lit
