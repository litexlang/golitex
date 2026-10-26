import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_square_x5f_set_x5f_membership_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M)))

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : (by
  let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_479 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_479 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))
  exact Litex.In _value_i1 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_7 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_2
                )
            )
          have h_8 : (by
            let _atomic_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_7 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_7 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_1_1 h_7 (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num)))
                )
            )
          have h_6 : Litex.In _value_i1 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_369 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_369 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _set := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_369 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_369 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))
                    exact (Litex.inSetBuilder_iff _value_i1 _set.val.bound _set.val.predicate).mpr ⟨h_7, h_8⟩)
                )
            )
          exact (by
          let _atomic_wd_1_1 := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_479 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_479 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))
          exact (Litex.inOfSame _value_i1 _value_i1 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_369 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_369 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
            let _left := (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_369 : Litex.In _value_i2 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i2 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_369 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))
            let _right := _atomic_wd_1_1
            exact (show Litex.Same _left _right from rfl)) h_6))
        )
      )
  )

theorem h_692 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ (M.powValue (Litex.denote _value_i1) (M.number (2 : ℂ))) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (((Litex.inSetBuilder_iff _value_i1 ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_610 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_610 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))).val.bound ((Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_610 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_610 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))).val.predicate).mp (Litex.inOfSame _value_i1 _value_i1 (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_610 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_610 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_610 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_610 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) (Litex.sameRefl _value_i1) (Litex.sameRefl (Litex.setBuilder (Litex.R (M := M)) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_610 : Litex.In _value_i3 (Litex.R (M := M))) => Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_610 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))))) (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)))).choose_spec
      )
  )

theorem h_693 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) : (by
  let _atomic_wd_1_1 := ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_610 : Litex.In _value_i3 (Litex.R (M := M))) => (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_610 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_2)
  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := ((fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_610 : Litex.In _value_i3 (Litex.R (M := M))) => (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_610 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.semanticObject (Litex.denote _value_i1) (Litex.isSet _value_i1)) h_2)
          exact (h_692 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_square_x5f_set_x5f_membership_x2f_statement_x2e_lit
