import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_multiplication_x5f_distributes_x5f_over_x5f_addition_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_15 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_16 : Litex.In _value_i2 (Litex.C (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_17 : Litex.In _value_i3 (Litex.C (M := M))), (by
  let _object_w2 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.add _value_i2 _value_i3 h_16 h_17);
  (Litex.mul _wd_1_0 _wd_1_1 h_15 (by
    let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 h_16 h_17)
    exact (Litex.addInC _value_i2 _value_i3 h_16 h_17))))
  let _object_w3 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 h_15 h_16);
  let _wd_1_1 := (Litex.mul _value_i1 _value_i3 h_15 h_17);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.mul _value_i1 _value_i2 h_15 h_16)
    exact (Litex.mulInC _value_i1 _value_i2 h_15 h_16)) (by
    let _atomic_wd_1_0 := (Litex.mul _value_i1 _value_i3 h_15 h_17)
    exact (Litex.mulInC _value_i1 _value_i3 h_15 h_17))))
  exact Litex.Same _object_w2 _object_w3
) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_15 _Host_i2 _rep_i2 _value_i2 h_16 _Host_i3 _rep_i3 _value_i3 h_17
    let _object_w2 := (let _wd_1_0 := _value_i1;
    let _wd_1_1 := (Litex.add _value_i2 _value_i3 h_16 h_17);
    (Litex.mul _wd_1_0 _wd_1_1 h_15 (by
      let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i3 h_16 h_17)
      exact (Litex.addInC _value_i2 _value_i3 h_16 h_17))))
    let _object_w3 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 h_15 h_16);
    let _wd_1_1 := (Litex.mul _value_i1 _value_i3 h_15 h_17);
    (Litex.add _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.mul _value_i1 _value_i2 h_15 h_16)
      exact (Litex.mulInC _value_i1 _value_i2 h_15 h_16)) (by
      let _atomic_wd_1_0 := (Litex.mul _value_i1 _value_i3 h_15 h_17)
      exact (Litex.mulInC _value_i1 _value_i3 h_15 h_17))))
    have h_1 : Litex.Same _object_w2 _object_w3 :=
      (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 h_15) * ((Litex.NativeBridge.asComplex _value_i2 h_16) + (Litex.NativeBridge.asComplex _value_i3 h_17))) (((Litex.NativeBridge.asComplex _value_i1 h_15) * (Litex.NativeBridge.asComplex _value_i2 h_16)) + ((Litex.NativeBridge.asComplex _value_i1 h_15) * (Litex.NativeBridge.asComplex _value_i3 h_17))) (Litex.NativeBridge.denoteMul _value_i1 (_object_w2).val.right (_object_w2).wd.1 (_object_w2).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.denoteAdd _value_i2 _value_i3 ((_object_w2).val.right).wd.1 ((_object_w2).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 h_16) (Litex.NativeBridge.asComplex_spec _value_i3 h_17))) (Litex.NativeBridge.denoteAdd (_object_w3).val.left (_object_w3).val.right (_object_w3).wd.1 (_object_w3).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i1 _value_i2 ((_object_w3).val.left).wd.1 ((_object_w3).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.asComplex_spec _value_i2 h_16)) (Litex.NativeBridge.denoteMul _value_i1 _value_i3 ((_object_w3).val.right).wd.1 ((_object_w3).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 h_15) (Litex.NativeBridge.asComplex_spec _value_i3 h_17))) (by ring!))
    exact h_1
  )
end LitexCompiled.file_lean_x2f_examples_x2f_multiplication_x5f_distributes_x5f_over_x5f_addition_x2f_statement_x2e_lit
