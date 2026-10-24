import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_rounding_x5f_integers_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

noncomputable def _object_w1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
(Litex.floor _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (3 : ℂ)) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (3 : ℂ)) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num))))))

noncomputable def _object_w2 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (-2 : ℂ) (- (2 : ℂ)) (let _round := _equal_wd_1_0;
        let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
        (Litex.roundingDenoteReal _round ((-3 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((- (3 : ℂ)) / (2 : ℂ)) = ((((-3 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.floor ((-3 : ℝ) / (2 : ℝ)) = (-2 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.floor ((-3 : ℝ) / (2 : ℝ)) : ℤ) : ℂ) = (-2 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (let _wd_1_0 := ((_object_w1 (M := M))).val.arg;
(Litex.ceil _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (3 : ℂ)) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_atomic_wd_1_0).val.left (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (3 : ℂ)) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num))))))

noncomputable def _object_w4 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_15 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  let _equal_wd_1_1 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        let _equal_wd_1_1 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (-1 : ℂ) (- (1 : ℂ)) (let _round := _equal_wd_1_0;
        let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
        (Litex.roundingDenoteReal _round ((-3 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteDiv ((_equal_wd_1_0).val.arg).val.left (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2.1 ((_equal_wd_1_0).val.arg).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((- (3 : ℂ)) / (2 : ℂ)) = ((((-3 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.ceil ((-3 : ℝ) / (2 : ℝ)) = (-1 : ℤ) := Int.ceil_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.ceil ((-3 : ℝ) / (2 : ℝ)) : ℤ) : ℂ) = (-1 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num))))
      )
  )

noncomputable def _object_w5 := (Litex.floor (Litex.number (M := M) (2.75 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2.75 : ℂ) (2.75 : ℝ) (by norm_num)))

theorem h_29 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (2 : ℂ) (let _round := _equal_wd_1_0;
        let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
        (Litex.roundingDenoteReal _round ((11 : ℝ) / (4 : ℝ)) (((Litex.NativeBridge.denoteNumber (M := M) (2.75 : ℂ))).trans (congrArg M.number (by norm_num : (2.75 : ℂ) = ((((11 : ℝ) / (4 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.floor ((11 : ℝ) / (4 : ℝ)) = (2 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.floor ((11 : ℝ) / (4 : ℝ)) : ℤ) : ℂ) = (2 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w7 := (Litex.ceil (Litex.number (M := M) (2.75 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2.75 : ℂ) (2.75 : ℝ) (by norm_num)))

theorem h_32 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (3 : ℂ) (let _round := _equal_wd_1_0;
        let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
        (Litex.roundingDenoteReal _round ((11 : ℝ) / (4 : ℝ)) (((Litex.NativeBridge.denoteNumber (M := M) (2.75 : ℂ))).trans (congrArg M.number (by norm_num : (2.75 : ℂ) = ((((11 : ℝ) / (4 : ℝ)) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.ceil ((11 : ℝ) / (4 : ℝ)) = (3 : ℤ) := Int.ceil_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.ceil ((11 : ℝ) / (4 : ℝ)) : ℤ) : ℂ) = (3 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w9 := (Litex.floor (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_35 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (let _round := _equal_wd_1_0;
        let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
        (Litex.roundingDenoteReal _round (0 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.floor (0 : ℝ) = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.floor (0 : ℝ) : ℤ) : ℂ) = (0 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w11 := (Litex.ceil (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_38 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (let _round := _equal_wd_1_0;
        let _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);
        (Litex.roundingDenoteReal _round (0 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℝ) : ℝ) : ℂ))))).trans (congrArg M.number (by have _value : Int.ceil (0 : ℝ) = (0 : ℤ) := Int.ceil_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.ceil (0 : ℝ) : ℤ) : ℂ) = (0 : ℂ); rw [_value]; norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

theorem h_45 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_58 : Litex.In _value_i1 (Litex.Z (M := M))), (by
  let _object_w13 := (Litex.floor _value_i1 (Litex.integerToReal _value_i1 h_58))
  have h_41 : (by
    let _equal_wd_1_0 := _object_w13
    exact Litex.Same _equal_wd_1_0 _value_i1) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := _object_w13;
          (show Litex.Same _equal_wd_1_0 _value_i1 from (by
            let _round := _equal_wd_1_0
            exact (Litex.roundingOfInteger _round h_58)
          )))
        )
    )
  let _object_w14 := (Litex.ceil _value_i1 (Litex.integerToReal _value_i1 h_58))
  have h_42 : (by
    let _equal_wd_1_0 := _object_w14
    exact Litex.Same _equal_wd_1_0 _value_i1) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := _object_w14;
          (show Litex.Same _equal_wd_1_0 _value_i1 from (by
            let _round := _equal_wd_1_0
            exact (Litex.roundingOfInteger _round h_58)
          )))
        )
    )
  let _object_w15 := (let _wd_1_0 := _object_w14;
  (Litex.floor _wd_1_0 (by
    let _atomic_wd_1_0 := _object_w14
    exact (Litex.integerToReal _atomic_wd_1_0 (Litex.inOfSame _value_i1 _atomic_wd_1_0 (Litex.Z (M := M)) (Litex.Z (M := M)) (h_42).symm (show @Eq M.Value _ _ from Eq.refl _) h_58)))))
  let _object_w16 := (let _wd_1_0 := _object_w13;
  (Litex.ceil _wd_1_0 (by
    let _atomic_wd_1_0 := _object_w13
    exact (Litex.integerToReal _atomic_wd_1_0 (Litex.inOfSame _value_i1 _atomic_wd_1_0 (Litex.Z (M := M)) (Litex.Z (M := M)) (h_41).symm (show @Eq M.Value _ _ from Eq.refl _) h_58)))))
  exact (((by
    let _equal_wd_1_0 := _object_w13
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w14
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w15
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((by
    let _equal_wd_1_0 := _object_w16
    exact Litex.Same _equal_wd_1_0 _value_i1)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_58
          let _object_w13 := (Litex.floor _value_i1 (Litex.integerToReal _value_i1 h_58))
          have h_41 : (by
            let _equal_wd_1_0 := _object_w13
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (by
                    let _round := _equal_wd_1_0
                    exact (Litex.roundingOfInteger _round h_58)
                  )))
                )
            )
          let _object_w14 := (Litex.ceil _value_i1 (Litex.integerToReal _value_i1 h_58))
          have h_42 : (by
            let _equal_wd_1_0 := _object_w14
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (by
                    let _round := _equal_wd_1_0
                    exact (Litex.roundingOfInteger _round h_58)
                  )))
                )
            )
          let _object_w15 := (let _wd_1_0 := _object_w14;
          (Litex.floor _wd_1_0 (by
            let _atomic_wd_1_0 := _object_w14
            exact (Litex.integerToReal _atomic_wd_1_0 (Litex.inOfSame _value_i1 _atomic_wd_1_0 (Litex.Z (M := M)) (Litex.Z (M := M)) (h_42).symm (show @Eq M.Value _ _ from Eq.refl _) h_58)))))
          have h_43 : (by
            let _equal_wd_1_0 := _object_w15
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (by
                    let _round := _equal_wd_1_0
                    exact ((Litex.roundingOfInteger _round (Litex.roundingInZ _round.val.arg)).trans (Litex.roundingOfInteger _round.val.arg h_58))
                  )))
                )
            )
          let _object_w16 := (let _wd_1_0 := _object_w13;
          (Litex.ceil _wd_1_0 (by
            let _atomic_wd_1_0 := _object_w13
            exact (Litex.integerToReal _atomic_wd_1_0 (Litex.inOfSame _value_i1 _atomic_wd_1_0 (Litex.Z (M := M)) (Litex.Z (M := M)) (h_41).symm (show @Eq M.Value _ _ from Eq.refl _) h_58)))))
          have h_44 : (by
            let _equal_wd_1_0 := _object_w16
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w16;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (by
                    let _round := _equal_wd_1_0
                    exact ((Litex.roundingOfInteger _round (Litex.roundingInZ _round.val.arg)).trans (Litex.roundingOfInteger _round.val.arg h_58))
                  )))
                )
            )
          exact (And.intro h_41 (And.intro h_42 (And.intro h_43 h_44)))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_rounding_x5f_integers_x2f_statement_x2e_lit
