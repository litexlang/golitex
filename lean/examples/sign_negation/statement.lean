import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sign_x5f_negation_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_9 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_22 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_22));
  (Litex.sign _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.negInR _value_i1 h_22))))
  let _object_w3 := (let _wd_1_0 := (Litex.sign _value_i1 h_22);
  (Litex.neg _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
  let _object_w4 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.numberInC (M := M) (0 : ℂ)) (M.real_subset_complex _ h_22));
  (Litex.sign _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.subInR (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_22))))
  let _object_w5 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
  let _wd_1_1 := (_object_w3).val.arg;
  (Litex.sub _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
  let _object_w6 := (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_2_1 := _value_i1;
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (M.real_subset_complex _ h_22)));
  (Litex.sign _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR (_atomic_wd_1_0).val.left _value_i1 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.left (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))) h_22))))
  let _object_w7 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_1_1 := (_object_w5).val.right;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
  let _object_w8 := (let _wd_1_0 := (let _wd_2_0 := _value_i1;
  let _wd_2_1 := ((_object_w6).val.arg).val.left;
  (Litex.mul _wd_2_0 _wd_2_1 (M.real_subset_complex _ h_22) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
  (Litex.sign _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR _value_i1 (_atomic_wd_1_0).val.right h_22 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.right (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))))))
  let _object_w9 := (let _wd_1_0 := (_object_w7).val.right;
  let _wd_1_1 := ((_object_w6).val.arg).val.left;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
  let _object_w10 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_1_1 := (_object_w9).val.left;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
  let _object_w11 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_2_1 := _value_i1;
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (M.real_subset_complex _ h_22)));
  (Litex.sign _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR (_atomic_wd_1_0).val.left _value_i1 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.left ((0 : ℂ) - (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) - (1 : ℂ)) (-1 : ℝ) (by norm_num))) h_22))))
  let _object_w12 := (let _wd_1_0 := (let _wd_2_0 := _value_i1;
  let _wd_2_1 := (_object_w10).val.left;
  (Litex.mul _wd_2_0 _wd_2_1 (M.real_subset_complex _ h_22) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
  (Litex.sign _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR _value_i1 (_atomic_wd_1_0).val.right h_22 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.right ((0 : ℂ) - (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) - (1 : ℂ)) (-1 : ℝ) (by norm_num)))))))
  let _object_w13 := (let _wd_1_0 := (_object_w10).val.right;
  let _wd_1_1 := (_object_w10).val.left;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
  exact (((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w11
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_22
          let _object_w2 := (let _wd_1_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_22));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i1 h_22))))
          let _object_w3 := (let _wd_1_0 := (Litex.sign _value_i1 h_22);
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
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
                    let _sign := (_equal_wd_1_1).val.arg
                    exact (((congrArg (Litex.signValue (M := M)) (Eq.refl (M.negValue (Litex.denote _sign.val.arg)))).trans (Litex.signNegation _sign)).trans ((Eq.refl (M.negValue (Litex.denote _sign)))).symm)
                  )))
                )
            )
          let _object_w4 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.numberInC (M := M) (0 : ℂ)) (M.real_subset_complex _ h_22));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_22))))
          let _object_w5 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_1 := (_object_w3).val.arg;
          (Litex.sub _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (0 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
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
                    let _sign := (_equal_wd_1_1).val.right
                    exact (((congrArg (Litex.signValue (M := M)) (Litex.zeroSubValue _sign.val.arg (Litex.realToComplex _sign.val.arg _sign.wd))).trans (Litex.signNegation _sign)).trans ((Litex.zeroSubValue _sign (Litex.integerToComplex _sign (Litex.signInZ _sign)))).symm)
                  )))
                )
            )
          let _object_w6 := (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_2_1 := _value_i1;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (M.real_subset_complex _ h_22)));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR (_atomic_wd_1_0).val.left _value_i1 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.left (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num))) h_22))))
          let _object_w7 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (_object_w5).val.right;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _sign := (_equal_wd_1_1).val.right
                    exact (((congrArg (Litex.signValue (M := M)) ((congrArg (fun _c => M.mulValue _c (Litex.denote _sign.val.arg)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.negOneMulValue _sign.val.arg (Litex.realToComplex _sign.val.arg _sign.wd)))).trans (Litex.signNegation _sign)).trans (((congrArg (fun _c => M.mulValue _c (Litex.denote _sign)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.negOneMulValue _sign (Litex.integerToComplex _sign (Litex.signInZ _sign))))).symm)
                  )))
                )
            )
          let _object_w8 := (let _wd_1_0 := (let _wd_2_0 := _value_i1;
          let _wd_2_1 := ((_object_w6).val.arg).val.left;
          (Litex.mul _wd_2_0 _wd_2_1 (M.real_subset_complex _ h_22) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR _value_i1 (_atomic_wd_1_0).val.right h_22 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.right (- (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (1 : ℂ)) (-1 : ℝ) (by norm_num)))))))
          let _object_w9 := (let _wd_1_0 := (_object_w7).val.right;
          let _wd_1_1 := ((_object_w6).val.arg).val.left;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w8
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w8;
                  let _equal_wd_1_1 := _object_w9;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _sign := (_equal_wd_1_1).val.left
                    exact (((congrArg (Litex.signValue (M := M)) ((congrArg (fun _c => M.mulValue (Litex.denote _sign.val.arg) _c) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.mulNegOneValue _sign.val.arg (Litex.realToComplex _sign.val.arg _sign.wd)))).trans (Litex.signNegation _sign)).trans (((congrArg (fun _c => M.mulValue (Litex.denote _sign) _c) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.mulNegOneValue _sign (Litex.integerToComplex _sign (Litex.signInZ _sign))))).symm)
                  )))
                )
            )
          let _object_w10 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_1 := (_object_w9).val.left;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
          let _object_w11 := (let _wd_1_0 := (let _wd_2_0 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_2_1 := _value_i1;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (M.real_subset_complex _ h_22)));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR (_atomic_wd_1_0).val.left _value_i1 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.left ((0 : ℂ) - (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) - (1 : ℂ)) (-1 : ℝ) (by norm_num))) h_22))))
          have h_5 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _sign := (_equal_wd_1_0).val.right
                    exact (((congrArg (Litex.signValue (M := M)) ((congrArg (fun _c => M.mulValue _c (Litex.denote _sign.val.arg)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.negOneMulValue _sign.val.arg (Litex.realToComplex _sign.val.arg _sign.wd)))).trans (Litex.signNegation _sign)).trans (((congrArg (fun _c => M.mulValue _c (Litex.denote _sign)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.negOneMulValue _sign (Litex.integerToComplex _sign (Litex.signInZ _sign))))).symm).symm
                  )))
                )
            )
          let _object_w12 := (let _wd_1_0 := (let _wd_2_0 := _value_i1;
          let _wd_2_1 := (_object_w10).val.left;
          (Litex.mul _wd_2_0 _wd_2_1 (M.real_subset_complex _ h_22) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR _value_i1 (_atomic_wd_1_0).val.right h_22 (Litex.NativeBridge.inOfDenoteNumber (_atomic_wd_1_0).val.right ((0 : ℂ) - (1 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.numberInROfEq ((0 : ℂ) - (1 : ℂ)) (-1 : ℝ) (by norm_num)))))))
          let _object_w13 := (let _wd_1_0 := (_object_w10).val.right;
          let _wd_1_1 := (_object_w10).val.left;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ))))))
          have h_6 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _sign := (_equal_wd_1_1).val.left
                    exact (((congrArg (Litex.signValue (M := M)) ((congrArg (fun _c => M.mulValue (Litex.denote _sign.val.arg) _c) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.mulNegOneValue _sign.val.arg (Litex.realToComplex _sign.val.arg _sign.wd)))).trans (Litex.signNegation _sign)).trans (((congrArg (fun _c => M.mulValue (Litex.denote _sign) _c) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.mulNegOneValue _sign (Litex.integerToComplex _sign (Litex.signInZ _sign))))).symm)
                  )))
                )
            )
          have h_7 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _sign := (_object_w13).val.left
                    exact (((congrArg (Litex.signValue (M := M)) (Eq.refl (M.negValue (Litex.denote _sign.val.arg)))).trans (Litex.signNegation _sign)).trans (((congrArg (fun _c => M.mulValue _c (Litex.denote _sign)) (((Litex.NativeBridge.denoteSub (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : ((0 : ℂ) - (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.negOneMulValue _sign (Litex.integerToComplex _sign (Litex.signInZ _sign))))).symm)
                  )
                )
            )
          have h_8 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _sign := (_object_w13).val.left
                    exact (((congrArg (Litex.signValue (M := M)) ((congrArg (fun _c => M.mulValue (Litex.denote _sign.val.arg) _c) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ))))).trans (Litex.mulNegOneValue _sign.val.arg (Litex.realToComplex _sign.val.arg _sign.wd)))).trans (Litex.signNegation _sign)).trans ((Litex.zeroSubValue _sign (Litex.integerToComplex _sign (Litex.signInZ _sign)))).symm).symm
                  )
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 (And.intro h_5 (And.intro h_6 (And.intro h_7 h_8)))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sign_x5f_negation_x2f_statement_x2e_lit
