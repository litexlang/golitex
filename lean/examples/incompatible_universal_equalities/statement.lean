import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_incompatible_x5f_universal_x5f_equalities_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∃ (_value_i1 : Litex.Obj (M := M) M.Value), ∃ (h_5 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), ((¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        by
          let _value_i1 : Litex.Obj (M := M) M.Value := Litex.semanticObject (Litex.denote (Litex.number (M := M) (0 : ℂ))) (Litex.isSet (Litex.number (M := M) (0 : ℂ)))
          have h_10 : Litex.In _value_i1 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) := (by
            let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact (by
              let _set := _atomic_wd_1_1
              exact ((Litex.inInsert_iff (Litex.number (M := M) (0 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _)))))
          have h_12 : Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) := rfl
          have h_15 : ((¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)))) := (by
            classical
            have _litex_sum_nonzero : (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.add _wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) ^ (2 : ℕ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) ^ (2 : ℕ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            (Litex.add _wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) ^ (2 : ℕ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) ^ (2 : ℕ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ))))))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((0 : ℂ) ^ (2 : ℕ)) + ((1 : ℂ) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            by_cases _litex_left : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ))
            · apply Or.inr
              intro _litex_right
              have _litex_x_zero : (0 : ℂ) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_left)
              have _litex_y_zero : (1 : ℂ) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_right.symm)
              apply _litex_sum_nonzero
              exact Litex.NativeBridge.sameOfDenoteNumber (let _wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) ^ (2 : ℕ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) ^ (2 : ℕ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))))) (Litex.number (M := M) (0 : ℂ)) (((0 : ℂ) ^ (2 : ℕ)) + ((1 : ℂ) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.powNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (by
            let _atomic_wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (0 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) ^ (2 : ℕ)) = (0 : ℂ)))) (Litex.numberInC (M := M) (0 : ℂ)))) (by
            let _atomic_wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) ^ (2 : ℕ)) = (1 : ℂ)))) (Litex.numberInC (M := M) (1 : ℂ)))) _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) ((congrArg₂ (fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)) _litex_x_zero _litex_y_zero).trans (by norm_num))
            · exact Or.inl _litex_left
          )
          exact ⟨_value_i1, h_10, h_15⟩
      )
  )

theorem h_53 : ¬ (∀ (_value_i2 : Litex.Obj (M := M) M.Value), (M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))) → (((((Litex.denote _value_i2) = (M.number (0 : ℂ)))) ∧ (((Litex.denote _value_i2) = (M.number (1 : ℂ))))))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          intro _universal
          have _counterexample : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_58 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0)), ((¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)))) := (h_4 (M := M))
          rcases _counterexample with ⟨_value_i2, h_58, h_56⟩
          have _positive : ((((Litex.denote _value_i2) = (M.number (0 : ℂ)))) ∧ (((Litex.denote _value_i2) = (M.number (1 : ℂ))))) := _universal _value_i2 h_58
          have _negative : (((¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) ∨ ((¬ ((Litex.denote _value_i2) = (M.number (1 : ℂ)))))) := h_56
          have _refute : ¬ (((((Litex.denote _value_i2) = (M.number (0 : ℂ)))) ∧ (((Litex.denote _value_i2) = (M.number (1 : ℂ)))))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using _negative
          exact _refute _positive)
      )
  )

theorem h_63 : ∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (h_58 : Litex.In _value_i2 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)), ((¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i2 (Litex.number (M := M) (1 : ℂ)))) :=
  (by
    litex_complete =>
      exact (
        (by
          classical
          have _counterexample : (∃ (_value_i2 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i2) (Litex.SetSemantics.insertValue (M.number (0 : ℂ)) (Litex.SetSemantics.emptyValue (M := M)))), (((¬ ((Litex.denote _value_i2) = (M.number (0 : ℂ))))) ∨ ((¬ ((Litex.denote _value_i2) = (M.number (1 : ℂ))))))) := by
            simpa only [not_forall, Classical.not_imp, not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc, exists_prop] using (h_53 (M := M))
          exact _counterexample)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_incompatible_x5f_universal_x5f_equalities_x2f_statement_x2e_lit
