import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_compound_x5f_theorem_x5f_returns_x2f_statement_x2e_lit

universe u v1 v3 v5
variable {M : Litex.Semantics.{u}}

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_10 : Litex.In _value_i1 (Litex.R (M := M))), ((((Litex.Same (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_10) (M.real_subset_complex _ h_10)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_10 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_10 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_10) (M.real_subset_complex _ h_10))))) ∧ (((Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_10 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_10) (M.real_subset_complex _ h_10)) (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_10 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_10
          have h_127 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          have h_6 : (by
            let _chain_wd_6_0 := (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127))
            let _chain_wd_6_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            let _chain_wd_6_2 := _chain_wd_6_1
            let _chain_wd_6_3 := _chain_wd_6_0
            exact ((by
              let _equal_wd_1_0 := _chain_wd_6_0
              let _equal_wd_1_1 := _chain_wd_6_1
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _chain_wd_6_2
              let _equal_wd_1_1 := _chain_wd_6_3
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _chain_wd_6_0 := (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127))
                    let _chain_wd_6_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    let _chain_wd_6_2 := _chain_wd_6_1
                    let _chain_wd_6_3 := _chain_wd_6_0
                    exact (And.intro (let _equal_wd_1_0 := _chain_wd_6_0;
                    let _equal_wd_1_1 := _chain_wd_6_1;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (by ring!)))) (let _equal_wd_1_0 := _chain_wd_6_2;
                    let _equal_wd_1_1 := _chain_wd_6_3;
                    (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) ^ (2 : ℕ)) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (by ring!))))))
                )
            )

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
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127))
            let _equal_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) :=
            (by
              litex_checked_step =>
                exact (
                  (And.intro (by
                    let _atomic_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_1_1 h_127 (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))) h_190)
                )
            )

          have h_7 :=
            (And.left h_9)

          have h_8 :=
            (And.right h_9)
          exact (And.intro (by
            let _chain_wd_1_0 := (Litex.mul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127))
            let _chain_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            let _chain_wd_1_2 := _chain_wd_1_1
            let _chain_wd_1_3 := _chain_wd_1_0
            exact (And.intro h_190 (h_190).symm)) (And.intro (by
            let _atomic_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact h_7) h_190))
        )
      )
  )

theorem h_1660 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_1662 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1662 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_1662
          have h_1693 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1662
                )
            )
          have h_1661 : (by
            have h_1694 : Litex.In _value_i3 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1693
                  )
              )
            exact (by
              let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1694 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_1694 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1693
                          )
                      )
                    have h_1695 : ((Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1694) (M.real_subset_complex _ h_1694)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1694 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1694 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1694) (M.real_subset_complex _ h_1694)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (And.left ((h_5 (M := M)) _value_i3 h_1694))
                          )
                      )
                    have h_1872 :=
                      (And.left h_1695)
                    have h_1873 :=
                      (And.right h_1695)
                    have h_1874 :=
                      h_1872
                    have h_1875 :=
                      h_1873
                    have h_2838 :=
                      (Eq.trans h_1872 h_1873)
                    have h_1698 : ((Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1694 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1694) (M.real_subset_complex _ h_1694)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1694 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (And.right ((h_5 (M := M)) _value_i3 h_1694))
                          )
                      )
                    have h_1696 :=
                      (And.left h_1698)
                    have h_1697 :=
                      (And.right h_1698)
                    exact (by
                    let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1694 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    exact h_1696)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1693 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact h_1661)
        )
      )
  )

theorem h_3475 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_3477 : Litex.In _value_i5 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3477) (M.real_subset_complex _ h_3477))
  let _equal_wd_1_1 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3477 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_3477
          have h_3506 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3477
                )
            )
          have h_3476 : (by
            have h_3507 : Litex.In _value_i5 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_3506
                  )
              )
            exact (by
              let _equal_wd_1_0 := (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3507) (M.real_subset_complex _ h_3507))
              let _equal_wd_1_1 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3507 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_3507 : Litex.In _value_i5 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3506
                          )
                      )
                    have h_3508 : ((Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3507) (M.real_subset_complex _ h_3507)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3507 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3507 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3507) (M.real_subset_complex _ h_3507)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (And.left ((h_5 (M := M)) _value_i5 h_3507))
                          )
                      )
                    have h_3685 :=
                      (And.left h_3508)
                    have h_3686 :=
                      (And.right h_3508)
                    have h_3687 :=
                      h_3685
                    have h_3688 :=
                      h_3686
                    have h_4651 :=
                      (Eq.trans h_3685 h_3686)
                    have h_3511 : ((Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3507 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3507) (M.real_subset_complex _ h_3507)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3507 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (And.right ((h_5 (M := M)) _value_i5 h_3507))
                          )
                      )
                    have h_3509 :=
                      (And.left h_3511)
                    have h_3510 :=
                      (And.right h_3511)
                    exact (let _equal_wd_1_0 := (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3507) (M.real_subset_complex _ h_3507));
                  let _equal_wd_1_1 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3507 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_3685).trans (Litex.sameRefl _equal_wd_1_1)))))
                  )
                )
            )
          exact h_3476
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_compound_x5f_theorem_x5f_returns_x2f_statement_x2e_lit
