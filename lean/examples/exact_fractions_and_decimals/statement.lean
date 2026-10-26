import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_exact_x5f_fractions_x5f_and_x5f_decimals_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_w1 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2)) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))))

noncomputable def _object_w2 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (((1 : ℂ) / (3 : ℂ)) + ((1 : ℂ) / (6 : ℂ))) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2.1 ((_equal_wd_1_0).val.left).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) ((_equal_wd_1_0).val.right).wd.1 ((_equal_wd_1_0).val.right).wd.2.1 ((_equal_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
      )
  )

theorem h_20 : (by
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same (Litex.number (M := M) (0.5 : ℂ)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same (Litex.number (M := M) (0.5 : ℂ)) _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0.5 : ℂ)) _equal_wd_1_1 (0.5 : ℂ) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0.5 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w2 (M := M))).wd.1 ((_object_w2 (M := M))).wd.2.1 ((_object_w2 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
      )
  )

noncomputable def _object_w4 := ((_object_w1 (M := M))).val.left

theorem h_22 : (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0.333 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w4 (M := M))
          exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0.333 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (0.333 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0.333 : ℂ)) (by norm_num)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_exact_x5f_fractions_x5f_and_x5f_decimals_x2f_statement_x2e_lit
