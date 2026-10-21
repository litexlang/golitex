import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_cancellation_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.C (M := M))) (h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (let _wd_1_0 := (Litex.div _value_i1 _value_i2 h_16 h_17 h_1);
  let _wd_1_1 := _value_i2;
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.divInC _value_i1 _wd_1_1 h_16 h_17 (_wd_1_0).wd.2.2) h_17))
  exact Litex.Same _object_w3 _value_i1
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 h_1
    let _object_w3 := (let _wd_1_0 := (Litex.div _value_i1 _value_i2 h_16 h_17 h_1);
    let _wd_1_1 := _value_i2;
    (Litex.mul _wd_1_0 _wd_1_1 (Litex.divInC _value_i1 _wd_1_1 h_16 h_17 (_wd_1_0).wd.2.2) h_17))
    have h_2 : Litex.Same _object_w3 _value_i1 :=
      (Litex.NativeBridge.sameOfDenoteNumber _object_w3 _value_i1 (((Litex.NativeBridge.asComplex _value_i1 h_16) / (Litex.NativeBridge.asComplex _value_i2 h_17)) * (Litex.NativeBridge.asComplex _value_i2 h_17)) (Litex.NativeBridge.asComplex _value_i1 h_16) (Litex.NativeBridge.denoteMul (_object_w3).val.left _value_i2 (_object_w3).wd.1 (_object_w3).wd.2 _ _ (Litex.NativeBridge.denoteDiv _value_i1 _value_i2 ((_object_w3).val.left).wd.1 ((_object_w3).val.left).wd.2.1 ((_object_w3).val.left).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_16) (Litex.NativeBridge.asComplex_spec _value_i2 h_17)) (Litex.NativeBridge.asComplex_spec _value_i2 h_17)) (Litex.NativeBridge.asComplex_spec _value_i1 h_16) (((div_eq_iff (Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 h_17) (Litex.NativeBridge.asComplex_spec _value_i2 h_17) ((_object_w3).val.left).wd.2.2)).mp (Litex.NativeBridge.nativeEqOfDenoteNumber (_object_w3).val.left (_object_w3).val.left ((Litex.NativeBridge.asComplex _value_i1 h_16) / (Litex.NativeBridge.asComplex _value_i2 h_17)) ((Litex.NativeBridge.asComplex _value_i1 h_16) / (Litex.NativeBridge.asComplex _value_i2 h_17)) (Litex.NativeBridge.denoteDiv _value_i1 _value_i2 h_16 h_17 h_1 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_16) (Litex.NativeBridge.asComplex_spec _value_i2 h_17)) (Litex.NativeBridge.denoteDiv _value_i1 _value_i2 h_16 h_17 h_1 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_16) (Litex.NativeBridge.asComplex_spec _value_i2 h_17)) (show @Eq M.Value _ _ from Eq.refl _))).symm))
    exact h_2
  )
end LitexCompiled.file_lean_x2f_examples_x2f_division_x5f_cancellation_x2f_statement_x2e_lit
