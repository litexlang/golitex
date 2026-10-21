import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_exact_x5f_fractions_x5f_and_x5f_decimals_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_w1 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (3 : ℂ))))) (by
  let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (6 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (6 : ℂ)) = ((1 : ℂ) / (6 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (6 : ℂ)))))))

noncomputable def _object_w2 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_1 : Litex.Same (_object_w1 (M := M)) (_object_w2 (M := M)) :=
  (Litex.NativeBridge.sameOfDenoteNumber (_object_w1 (M := M)) (_object_w2 (M := M)) (((1 : ℂ) / (3 : ℂ)) + ((1 : ℂ) / (6 : ℂ))) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteAdd ((_object_w1 (M := M))).val.left ((_object_w1 (M := M))).val.right ((_object_w1 (M := M))).wd.1 ((_object_w1 (M := M))).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (((_object_w1 (M := M))).val.left).wd.1 (((_object_w1 (M := M))).val.left).wd.2.1 (((_object_w1 (M := M))).val.left).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (6 : ℂ)) (((_object_w1 (M := M))).val.right).wd.1 (((_object_w1 (M := M))).val.right).wd.2.1 (((_object_w1 (M := M))).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w2 (M := M))).wd.1 ((_object_w2 (M := M))).wd.2.1 ((_object_w2 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))

theorem h_20 : Litex.Same (Litex.number (M := M) (0.5 : ℂ)) (_object_w2 (M := M)) :=
  (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0.5 : ℂ)) (_object_w2 (M := M)) (0.5 : ℂ) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0.5 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_object_w2 (M := M))).wd.1 ((_object_w2 (M := M))).wd.2.1 ((_object_w2 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))

noncomputable def _object_w4 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_22 : (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0.333 : ℂ))) :=
  (by
    let _atomic_wd_1_0 := (_object_w4 (M := M))
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0.333 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (0.333 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0.333 : ℂ)) (by norm_num)))
end LitexCompiled.file_lean_x2f_examples_x2f_exact_x5f_fractions_x5f_and_x5f_decimals_x2f_statement_x2e_lit
