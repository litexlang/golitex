import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_definitions_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_18 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (Litex.sinh _value_i1 h_18)
  let _object_w3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.exp _value_i1 h_18);
  let _wd_2_1 := (let _wd_3_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_18));
  (Litex.exp _wd_3_0 (by
    let _atomic_wd_1_0 := _wd_3_0
    exact (Litex.negInR _value_i1 h_18))));
  (Litex.sub _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (Litex.exp _value_i1 h_18)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (let _wd_3_0 := (_wd_2_1).val.arg;
    (Litex.exp _wd_3_0 (by
      let _atomic_wd_2_0 := _wd_3_0
      exact (Litex.negInR _value_i1 h_18))))
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0)))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.exp _value_i1 h_18);
    let _wd_2_1 := (let _wd_3_0 := ((_wd_1_0).val.right).val.arg;
    (Litex.exp _wd_3_0 (by
      let _atomic_wd_2_0 := _wd_3_0
      exact (Litex.negInR _value_i1 h_18))));
    (Litex.sub _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := (Litex.exp _value_i1 h_18)
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.expInRPos _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_1).val.arg;
      (Litex.exp _wd_3_0 (by
        let _atomic_wd_3_0 := _wd_3_0
        exact (Litex.negInR _value_i1 h_18))))
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.expInRPos _atomic_wd_2_0)))))
    exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex (_atomic_wd_1_0).val.left (Litex.expInRPos (_atomic_wd_1_0).val.left)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.expInRPos (_atomic_wd_1_0).val.right)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
  let _object_w4 := (Litex.cosh _value_i1 h_18)
  let _object_w5 := (let _wd_1_0 := (let _wd_2_0 := (Litex.exp _value_i1 h_18);
  let _wd_2_1 := (let _wd_3_0 := (((_object_w3).val.left).val.right).val.arg;
  (Litex.exp _wd_3_0 (by
    let _atomic_wd_1_0 := _wd_3_0
    exact (Litex.negInR _value_i1 h_18))));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := (Litex.exp _value_i1 h_18)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (let _wd_3_0 := (_wd_2_1).val.arg;
    (Litex.exp _wd_3_0 (by
      let _atomic_wd_2_0 := _wd_3_0
      exact (Litex.negInR _value_i1 h_18))))
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0)))));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.exp _value_i1 h_18);
    let _wd_2_1 := (let _wd_3_0 := ((_wd_1_0).val.right).val.arg;
    (Litex.exp _wd_3_0 (by
      let _atomic_wd_2_0 := _wd_3_0
      exact (Litex.negInR _value_i1 h_18))));
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_2_0 := (Litex.exp _value_i1 h_18)
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.expInRPos _atomic_wd_2_0))) (by
      let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_1).val.arg;
      (Litex.exp _wd_3_0 (by
        let _atomic_wd_3_0 := _wd_3_0
        exact (Litex.negInR _value_i1 h_18))))
      exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.expInRPos _atomic_wd_2_0)))))
    exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex (_atomic_wd_1_0).val.left (Litex.expInRPos (_atomic_wd_1_0).val.left)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.expInRPos (_atomic_wd_1_0).val.right)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
  let _object_w6 := (Litex.tanh _value_i1 h_18)
  let _object_w7 := (let _wd_1_0 := _object_w2;
  let _wd_1_1 := _object_w4;
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _object_w2
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _object_w4
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _object_w4
    exact (fun _same => (Litex.coshNonzero _atomic_wd_1_0) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
  let _object_w8 := (Litex.sech _value_i1 h_18)
  let _object_w9 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := _object_w4;
  (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
    let _atomic_wd_1_0 := _object_w4
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _object_w4
    exact (fun _same => (Litex.coshNonzero _atomic_wd_1_0) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
  exact (((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_18
          let _object_w2 := (Litex.sinh _value_i1 h_18)
          let _object_w3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.exp _value_i1 h_18);
          let _wd_2_1 := (let _wd_3_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_18));
          (Litex.exp _wd_3_0 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (Litex.negInR _value_i1 h_18))));
          (Litex.sub _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := (Litex.exp _value_i1 h_18)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (let _wd_3_0 := (_wd_2_1).val.arg;
            (Litex.exp _wd_3_0 (by
              let _atomic_wd_2_0 := _wd_3_0
              exact (Litex.negInR _value_i1 h_18))))
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0)))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.exp _value_i1 h_18);
            let _wd_2_1 := (let _wd_3_0 := ((_wd_1_0).val.right).val.arg;
            (Litex.exp _wd_3_0 (by
              let _atomic_wd_2_0 := _wd_3_0
              exact (Litex.negInR _value_i1 h_18))));
            (Litex.sub _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := (Litex.exp _value_i1 h_18)
              exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.expInRPos _atomic_wd_2_0))) (by
              let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_1).val.arg;
              (Litex.exp _wd_3_0 (by
                let _atomic_wd_3_0 := _wd_3_0
                exact (Litex.negInR _value_i1 h_18))))
              exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.expInRPos _atomic_wd_2_0)))))
            exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex (_atomic_wd_1_0).val.left (Litex.expInRPos (_atomic_wd_1_0).val.left)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.expInRPos (_atomic_wd_1_0).val.right)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    have _definition := Litex.sinhDefinition _equal_wd_1_0
                    change ((Litex.realUnaryValue (M := M) Real.sinh) (Litex.denote _value_i1)) = (M.divValue (M.subValue ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i1)) ((Litex.realUnaryValue (M := M) Real.exp) (M.negValue (Litex.denote _value_i1)))) (M.number (2 : ℂ))) at _definition
                    exact _definition)))
                )
            )
          let _object_w4 := (Litex.cosh _value_i1 h_18)
          let _object_w5 := (let _wd_1_0 := (let _wd_2_0 := (Litex.exp _value_i1 h_18);
          let _wd_2_1 := (let _wd_3_0 := (((_object_w3).val.left).val.right).val.arg;
          (Litex.exp _wd_3_0 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (Litex.negInR _value_i1 h_18))));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := (Litex.exp _value_i1 h_18)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (let _wd_3_0 := (_wd_2_1).val.arg;
            (Litex.exp _wd_3_0 (by
              let _atomic_wd_2_0 := _wd_3_0
              exact (Litex.negInR _value_i1 h_18))))
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0)))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.exp _value_i1 h_18);
            let _wd_2_1 := (let _wd_3_0 := ((_wd_1_0).val.right).val.arg;
            (Litex.exp _wd_3_0 (by
              let _atomic_wd_2_0 := _wd_3_0
              exact (Litex.negInR _value_i1 h_18))));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := (Litex.exp _value_i1 h_18)
              exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.expInRPos _atomic_wd_2_0))) (by
              let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_1).val.arg;
              (Litex.exp _wd_3_0 (by
                let _atomic_wd_3_0 := _wd_3_0
                exact (Litex.negInR _value_i1 h_18))))
              exact (Litex.positiveRealToComplex _atomic_wd_2_0 (Litex.expInRPos _atomic_wd_2_0)))))
            exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.positiveRealToComplex (_atomic_wd_1_0).val.left (Litex.expInRPos (_atomic_wd_1_0).val.left)) (Litex.positiveRealToComplex (_atomic_wd_1_0).val.right (Litex.expInRPos (_atomic_wd_1_0).val.right)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    have _definition := Litex.coshDefinition _equal_wd_1_0
                    change ((Litex.realUnaryValue (M := M) Real.cosh) (Litex.denote _value_i1)) = (M.divValue (M.addValue ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i1)) ((Litex.realUnaryValue (M := M) Real.exp) (M.negValue (Litex.denote _value_i1)))) (M.number (2 : ℂ))) at _definition
                    exact _definition)))
                )
            )
          let _object_w6 := (Litex.tanh _value_i1 h_18)
          let _object_w7 := (let _wd_1_0 := _object_w2;
          let _wd_1_1 := _object_w4;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w2
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _object_w4
            exact (fun _same => (Litex.coshNonzero _atomic_wd_1_0) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Real.tanh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ) ((Real.sinh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ) / (Real.cosh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteTanh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (let _hyp := _object_w2; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)))) (let _hyp := _object_w4; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18))))) (by simp only [Real.tanh_eq_sinh_div_cosh, Complex.ofReal_div]))))
                )
            )
          let _object_w8 := (Litex.sech _value_i1 h_18)
          let _object_w9 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := _object_w4;
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _object_w4
            exact (fun _same => (Litex.coshNonzero _atomic_wd_1_0) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w8
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w8;
                  let _equal_wd_1_1 := _object_w9;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeSech ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ) ((1 : ℂ) / (Real.cosh ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteSech _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (let _hyp := _object_w4; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i1 (Litex.realToComplex _value_i1 h_18)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.realToComplex _value_i1 h_18))))) (by simp only [Litex.nativeSech, Complex.ofReal_div, Complex.ofReal_one]))))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 h_4)))
        )
      )
  )

theorem h_1003 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_1016 : Litex.In _value_i2 (Litex.R (M := M))) (h_1000 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w12 := (Litex.coth _value_i2 h_1016 h_1000)
  let _object_w13 := (let _wd_1_0 := (Litex.cosh _value_i2 h_1016);
  let _wd_1_1 := (Litex.sinh _value_i2 h_1016);
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.cosh _value_i2 h_1016)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_1016)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_1016)
    exact (fun _same => (Litex.sinhNonzero _atomic_wd_1_0 h_1000) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
  let _object_w14 := (Litex.csch _value_i2 h_1016 h_1000)
  let _object_w15 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_1_1 := (Litex.sinh _value_i2 h_1016);
  (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_1016)
    exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_1016)
    exact (fun _same => (Litex.sinhNonzero _atomic_wd_1_0 h_1000) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
  exact (((by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w14
    let _equal_wd_1_1 := _object_w15
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_1016 h_1000
          let _object_w12 := (Litex.coth _value_i2 h_1016 h_1000)
          let _object_w13 := (let _wd_1_0 := (Litex.cosh _value_i2 h_1016);
          let _wd_1_1 := (Litex.sinh _value_i2 h_1016);
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.cosh _value_i2 h_1016)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.coshInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_1016)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_1016)
            exact (fun _same => (Litex.sinhNonzero _atomic_wd_1_0 h_1000) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
          have h_1001 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeCoth ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re : ℂ) ((Real.cosh ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re : ℂ) / (Real.sinh ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteCoth _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_1016)))) (Litex.NativeBridge.denoteDiv (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (let _hyp := (_equal_wd_1_1).val.left; Litex.denoteCosh _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_1016)))) (let _hyp := (_equal_wd_1_1).val.right; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_1016))))) (by simp only [Litex.nativeCoth, Complex.ofReal_div]))))
                )
            )
          let _object_w14 := (Litex.csch _value_i2 h_1016 h_1000)
          let _object_w15 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.sinh _value_i2 h_1016);
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_1016)
            exact (M.real_subset_complex _ (Litex.sinhInR _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.sinh _value_i2 h_1016)
            exact (fun _same => (Litex.sinhNonzero _atomic_wd_1_0 h_1000) (_same.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))))
          have h_1002 : (by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w14;
                  let _equal_wd_1_1 := _object_w15;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Litex.nativeCsch ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re : ℂ) ((1 : ℂ) / (Real.sinh ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re : ℂ)) (let _hyp := _equal_wd_1_0; Litex.denoteCsch _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016)) _hyp.wd.1 (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_1016)))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (let _hyp := (_equal_wd_1_1).val.right; Litex.denoteSinh _hyp ((Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016))).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (Litex.NativeBridge.asComplex _value_i2 (Litex.realToComplex _value_i2 h_1016)) _hyp.wd (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.realToComplex _value_i2 h_1016))))) (by simp only [Litex.nativeCsch, Complex.ofReal_div, Complex.ofReal_one]))))
                )
            )
          exact (And.intro h_1001 h_1002)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_definitions_x2f_statement_x2e_lit
