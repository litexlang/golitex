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

          have h_188 :=
            (And.left h_6)

          have h_189 :=
            (And.right h_6)

          have h_190 :=
            h_188

          have h_191 :=
            h_189

          have h_886 :=
            (Eq.trans h_188 h_189)
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
                    exact (Litex.powStructuralNonnegativeOfEven _atomic_wd_1_1 h_127 (2 : ℕ) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) (by norm_num))) (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127) _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (by ring!)))
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
            exact (And.intro (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127) _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (by ring!)) (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) ^ (2 : ℕ)) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127) _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (by ring!)))) (And.intro (by
            let _atomic_wd_1_1 := (Litex.powNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact h_7) (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) * (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127))) ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_127)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i1 _value_i1 (M.real_subset_complex _ h_127) (M.real_subset_complex _ h_127) _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127)) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (Litex.NativeBridge.denotePowNatReal _value_i1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_127 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_127))) (by ring!))))
        )
      )
  )

theorem h_1658 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_1660 : Litex.In _value_i3 (Litex.R (M := M))), (by
  let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1660 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_1660
          have h_1691 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1660
                )
            )
          have h_1659 : (by
            have h_1692 : Litex.In _value_i3 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_1691
                  )
              )
            exact (by
              let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1692 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_1692 : Litex.In _value_i3 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_1691
                          )
                      )
                    have h_1693 : ((Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1692) (M.real_subset_complex _ h_1692)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1692 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1692 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1692) (M.real_subset_complex _ h_1692)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (And.left ((h_5 (M := M)) _value_i3 h_1692))
                          )
                      )
                    have h_1870 :=
                      (And.left h_1693)
                    have h_1871 :=
                      (And.right h_1693)
                    have h_1872 :=
                      h_1870
                    have h_1873 :=
                      h_1871
                    have h_2836 :=
                      (Eq.trans h_1870 h_1871)
                    have h_1696 : ((Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1692 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.mul _value_i3 _value_i3 (M.real_subset_complex _ h_1692) (M.real_subset_complex _ h_1692)) (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1692 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (And.right ((h_5 (M := M)) _value_i3 h_1692))
                          )
                      )
                    have h_1694 :=
                      (And.left h_1696)
                    have h_1695 :=
                      (And.right h_1696)
                    exact (by
                    let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1692 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
                    exact h_1694)
                  )
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.powNatReal _value_i3 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_1691 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact h_1659)
        )
      )
  )

theorem h_3473 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_3475 : Litex.In _value_i5 (Litex.R (M := M))), (by
  let _equal_wd_1_0 := (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3475) (M.real_subset_complex _ h_3475))
  let _equal_wd_1_1 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3475 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_3475
          have h_3504 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_3475
                )
            )
          have h_3474 : (by
            have h_3505 : Litex.In _value_i5 (Litex.R (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    h_3504
                  )
              )
            exact (by
              let _equal_wd_1_0 := (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3505) (M.real_subset_complex _ h_3505))
              let _equal_wd_1_1 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3505 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
          ) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_3505 : Litex.In _value_i5 (Litex.R (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_3504
                          )
                      )
                    have h_3506 : ((Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3505) (M.real_subset_complex _ h_3505)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3505 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3505 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3505) (M.real_subset_complex _ h_3505)))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (And.left ((h_5 (M := M)) _value_i5 h_3505))
                          )
                      )
                    have h_3683 :=
                      (And.left h_3506)
                    have h_3684 :=
                      (And.right h_3506)
                    have h_3685 :=
                      h_3683
                    have h_3686 :=
                      h_3684
                    have h_4649 :=
                      (Eq.trans h_3683 h_3684)
                    have h_3509 : ((Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3505 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) ∧ (Litex.Same (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3505) (M.real_subset_complex _ h_3505)) (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3505 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (And.right ((h_5 (M := M)) _value_i5 h_3505))
                          )
                      )
                    have h_3507 :=
                      (And.left h_3509)
                    have h_3508 :=
                      (And.right h_3509)
                    exact (let _equal_wd_1_0 := (Litex.mul _value_i5 _value_i5 (M.real_subset_complex _ h_3505) (M.real_subset_complex _ h_3505));
                  let _equal_wd_1_1 := (Litex.powNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3505 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_3683).trans (Litex.sameRefl _equal_wd_1_1)))))
                  )
                )
            )
          exact (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_3504)) * (Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_3504))) ((Litex.NativeBridge.asComplex _value_i5 (Litex.realToComplex _value_i5 h_3504)) ^ (2 : ℕ)) (Litex.NativeBridge.denoteMul _value_i5 _value_i5 (M.real_subset_complex _ h_3504) (M.real_subset_complex _ h_3504) _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_3504)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_3504))) (Litex.NativeBridge.denotePowNatReal _value_i5 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) h_3504 (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.realToComplex _value_i5 h_3504))) (by ring!))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_compound_x5f_theorem_x5f_returns_x2f_statement_x2e_lit
