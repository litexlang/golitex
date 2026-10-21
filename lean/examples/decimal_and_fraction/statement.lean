import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_decimal_x5f_and_x5f_fraction_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))), (by
  let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (0.125 : ℂ)) h_15 (Litex.numberInC (M := M) (0.125 : ℂ)))
  let _object_w3 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.add _wd_1_0 _wd_1_1 h_15 (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((1 : ℂ) / (8 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (8 : ℂ)) = ((1 : ℂ) / (8 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (8 : ℂ))))))
  exact Litex.Same _object_w2 _object_w3
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15
    let _object_w2 := (Litex.add _value_i1 (Litex.number (M := M) (0.125 : ℂ)) h_15 (Litex.numberInC (M := M) (0.125 : ℂ)))
    let _object_w3 := (let _wd_1_0 := _value_i1;
    let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (Litex.add _wd_1_0 _wd_1_1 h_15 (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((1 : ℂ) / (8 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (8 : ℂ)) = ((1 : ℂ) / (8 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (8 : ℂ))))))
    have h_1 : Litex.Same _object_w2 _object_w3 :=
      (congrArg₂ M.addValue (show @Eq M.Value _ _ from Eq.refl _) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (0.125 : ℂ)) (_object_w3).val.right (0.125 : ℂ) ((1 : ℂ) / (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0.125 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ))) (by norm_num)))
    have h_76 : Litex.Same (Litex.number (M := M) (0.125 : ℂ)) (_object_w3).val.right :=
      (Litex.addCancelLeftLeft (Litex.number (M := M) (0.125 : ℂ)) (_object_w3).val.right _value_i1 (Litex.numberInC (M := M) (0.125 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (_object_w3).val.right ((1 : ℂ) / (8 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (8 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (8 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (8 : ℂ)) = ((1 : ℂ) / (8 : ℂ))))) (Litex.numberInC (M := M) ((1 : ℂ) / (8 : ℂ)))) h_15 h_1)
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_decimal_x5f_and_x5f_fraction_x2f_statement_x2e_lit
