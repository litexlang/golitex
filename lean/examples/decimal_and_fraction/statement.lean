import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_decimal_x5f_and_x5f_fraction_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (0.125 : ℂ)) h_15 (Litex.numberInC (M := M) (0.125 : ℂ)))
  let _object_w3 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.add _wd_1_0 _wd_1_1 h_15 (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (8 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (8 : ℂ)) = ((1 : ℂ) / (8 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (8 : ℂ)))))))
  exact (by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15
    let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (0.125 : ℂ)) h_15 (Litex.numberInC (M := M) (0.125 : ℂ)))
    let _object_w3 := (let _wd_1_0 := _value_i1;
    let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (Litex.add _wd_1_0 _wd_1_1 h_15 (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (8 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (8 : ℂ)) = ((1 : ℂ) / (8 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (8 : ℂ)))))))
    have h_1 : (by
      let _equal_wd_1_0 := _object_w2
      let _equal_wd_1_1 := _object_w3
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := _object_w2;
            let _equal_wd_1_1 := _object_w3;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (congrArg₂ M.addValue (show (Litex.denote _value_i1) = (Litex.denote _value_i1) from (show @Eq M.Value _ _ from Eq.refl _)) (show (M.number (0.125 : ℂ)) = (M.divValue (M.number (1 : ℂ)) (M.number (8 : ℂ))) from (let _equal_wd_2_1 := (_equal_wd_1_1).val.right;
            (show Litex.Same (Litex.number (M := M) (0.125 : ℂ)) _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0.125 : ℂ)) _equal_wd_2_1 (0.125 : ℂ) ((1 : ℂ) / (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0.125 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ))) (by norm_num))))))))
          )
      )
    have h_76 : Litex.Same (Litex.number (M := M) (0.125 : ℂ)) (_object_w3).val.right :=
      (by
        litex_checked_step =>
          exact (
            (Litex.addCancelLeftLeft (Litex.number (M := M) (0.125 : ℂ)) (_object_w3).val.right _value_i1 (Litex.numberInC (M := M) (0.125 : ℂ)) (by
              let _atomic_wd_1_0 := (_object_w3).val.right
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (8 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (8 : ℂ)) = ((1 : ℂ) / (8 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (8 : ℂ))))) h_15 h_1)
          )
      )
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_decimal_x5f_and_x5f_fraction_x2f_statement_x2e_lit
