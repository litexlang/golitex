import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_compound_x5f_theorem_x5f_returns_x2f_statement_x2e_lit

universe u v1 v3 v5
variable {M : Litex.Semantics.{u}}

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (Litex.R (M := M))), ((((Litex.Same (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_10) (M.real_subset_complex _ h_10)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_10 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_10 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_10) (M.real_subset_complex _ h_10))))) ∧ (((Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_10 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_10) (M.real_subset_complex _ h_10)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_10 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))))) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_10
    have h_127 : Litex.In _value_i1 (Litex.R (M := M)) :=
      h_10
    have h_6 : (Litex.Same (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127))) :=
      (And.intro (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127) _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (by ring!)) (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) ^ (2 : ℕ)) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127) _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (by ring!)))

    have h_190 :=
      (And.left h_6)

    have h_191 :=
      (And.right h_6)

    have h_192 :=
      h_190

    have h_193 :=
      h_191

    have h_888 :=
      (Eq.trans h_190 h_191)
    have h_9 : ((by
      let _atomic_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
      exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)) ∧ (Litex.Same (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) :=
      (And.intro (by
        let _atomic_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
        exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_1_1 h_127 (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))) h_190)

    have h_7 :=
      (And.left h_9)

    have h_8 :=
      (And.right h_9)
    exact (And.intro (And.intro h_190 (h_190).symm) (And.intro (by
      let _atomic_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
      exact h_7) h_190))
  )

theorem h_1740 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_1742 : Litex.In _value_i3 (Litex.R (M := M))), Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1742 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_1742
    have h_1773 : Litex.In _value_i3 (Litex.R (M := M)) :=
      h_1742
    have h_1741 : (by
      have h_1774 : Litex.In _value_i3 (Litex.R (M := M)) :=
        h_1773
      exact (by
        let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1774 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
        exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
    ) :=
      (by
        have h_1774 : Litex.In _value_i3 (Litex.R (M := M)) :=
          h_1773
        have h_1775 : ((Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1774) (M.real_subset_complex _ h_1774)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1774 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1774 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1774) (M.real_subset_complex _ h_1774)))) :=
          (And.left ((h_5 (M := M)) _value_i3 h_1774))
        have h_1952 :=
          (And.left h_1775)
        have h_1953 :=
          (And.right h_1775)
        have h_1954 :=
          h_1952
        have h_1955 :=
          h_1953
        have h_2918 :=
          (Eq.trans h_1952 h_1953)
        have h_1778 : ((Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1774 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1774) (M.real_subset_complex _ h_1774)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1774 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) :=
          (And.right ((h_5 (M := M)) _value_i3 h_1774))
        have h_1776 :=
          (And.left h_1778)
        have h_1777 :=
          (And.right h_1778)
        exact (by
        let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1774 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
        exact h_1776)
      )
    exact h_1741
  )

theorem h_3555 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_3557 : Litex.In _value_i5 (Litex.R (M := M))), Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3557) (M.real_subset_complex _ h_3557)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3557 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) :=
  (by
    intro _Host_i5 _rep_i5 _value_i5 h_3557
    have h_3586 : Litex.In _value_i5 (Litex.R (M := M)) :=
      h_3557
    have h_3556 : (by
      have h_3587 : Litex.In _value_i5 (Litex.R (M := M)) :=
        h_3586
      exact Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3587) (M.real_subset_complex _ h_3587)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3587 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
    ) :=
      (by
        have h_3587 : Litex.In _value_i5 (Litex.R (M := M)) :=
          h_3586
        have h_3588 : ((Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3587) (M.real_subset_complex _ h_3587)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3587 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3587 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3587) (M.real_subset_complex _ h_3587)))) :=
          (And.left ((h_5 (M := M)) _value_i5 h_3587))
        have h_3765 :=
          (And.left h_3588)
        have h_3766 :=
          (And.right h_3588)
        have h_3767 :=
          h_3765
        have h_3768 :=
          h_3766
        have h_4731 :=
          (Eq.trans h_3765 h_3766)
        have h_3591 : ((Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3587 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3587) (M.real_subset_complex _ h_3587)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3587 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) :=
          (And.right ((h_5 (M := M)) _value_i5 h_3587))
        have h_3589 :=
          (And.left h_3591)
        have h_3590 :=
          (And.right h_3591)
        exact (((Litex.sameRefl (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3587) (M.real_subset_complex _ h_3587)))).symm.trans ((h_3765).trans (Litex.sameRefl (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3587 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))))
      )
    exact h_3556
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_compound_x5f_theorem_x5f_returns_x2f_statement_x2e_lit
