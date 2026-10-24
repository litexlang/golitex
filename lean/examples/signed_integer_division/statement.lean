import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_integer_x5f_division_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.quot (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (2 : ℂ) (let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.quotInZ _intop);
        (Litex.quotDenoteInt _intop (7 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = ((7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.quot _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))))

noncomputable def _object_w4 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))

theorem h_5 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  let _equal_wd_1_1 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        let _equal_wd_1_1 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (-3 : ℂ) (- (3 : ℂ)) (let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.quotInZ _intop);
        (Litex.quotDenoteInt _intop (-7 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_equal_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = ((-7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))))
      )
  )

noncomputable def _object_w5 := (Litex.mod (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_12 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.modInZ _intop);
        (Litex.modDenoteInt _intop (7 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = ((7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w7 := (let _wd_1_0 := ((_object_w3 (M := M))).val.left;
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.mod _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_17 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (2 : ℂ) (let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.modInZ _intop);
        (Litex.modDenoteInt _intop (-7 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_equal_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = ((-7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w8 := (let _wd_1_0 := (Litex.number (M := M) (7 : ℂ));
let _wd_1_1 := (_object_w4 (M := M));
(Litex.mod _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w4 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (3 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w4 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))

theorem h_24 : (by
  let _equal_wd_1_0 := (_object_w8 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w8 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.modInZ _intop);
        (Litex.modDenoteInt _intop (7 : ℤ) (-3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = ((7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w4 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = ((-3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w9 := (let _wd_1_0 := ((_object_w7 (M := M))).val.left;
let _wd_1_1 := (_object_w4 (M := M));
(Litex.mod _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w4 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := (_object_w4 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (3 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w4 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))

theorem h_29 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (2 : ℂ) (let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.modInZ _intop);
        (Litex.modDenoteInt _intop (-7 : ℤ) (-3 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_equal_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = ((-7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w4 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = ((-3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
      )
  )

theorem h_37 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_50 : Litex.In _value_i1 (Litex.Z (M := M))), (by
  let _object_w11 := (Litex.quot _value_i1 (Litex.number (M := M) (1 : ℂ)) h_50 (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num)))
  exact (by
    let _equal_wd_1_0 := _object_w11
    exact Litex.Same _equal_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_50
          let _object_w11 := (Litex.quot _value_i1 (Litex.number (M := M) (1 : ℂ)) h_50 (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num)))
          have h_36 : (by
            let _equal_wd_1_0 := _object_w11
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (by
                    let _quot := _equal_wd_1_0
                    exact (Litex.quotByOne _quot (Litex.sameRefl (Litex.number (M := M) 1)))
                  )))
                )
            )
          exact h_36
        )
      )
  )

theorem h_62 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_75 : Litex.In _value_i2 (Litex.NPos (M := M))), (by
  let _object_w14 := (Litex.quot _value_i2 _value_i2 (Litex.naturalToInteger _value_i2 (Litex.inNPos_natural _value_i2 h_75)) h_75)
  exact (by
    let _equal_wd_1_0 := _object_w14
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_75
          have h_76 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i2 h_75)
                )
            )
          have h_77 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_76)
                )
            )
          have h_78 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_76) _litex_zero.symm)
                )
            )
          let _object_w14 := (Litex.quot _value_i2 _value_i2 (Litex.naturalToInteger _value_i2 (Litex.inNPos_natural _value_i2 h_75)) h_75)
          have h_61 : (by
            let _equal_wd_1_0 := _object_w14
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (by
                    let _quot := _equal_wd_1_0
                    exact (Litex.quotSelfOne _quot (Litex.sameRefl _quot.val.left) h_75)
                  )))
                )
            )
          exact h_61
        )
      )
  )

theorem h_104 : Litex.IsNonempty (Litex.Z (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.integer)

variable {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.Z (M := M)))

theorem h_106 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.Z (M := M))) : Litex.IsNonempty (Litex.NPos (M := M)) := (Litex.nPosNonempty (M := M))

variable {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_107 : Litex.In _value_i4 (Litex.NPos (M := M)))

theorem h_108 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.Z (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_107 : Litex.In _value_i4 (Litex.NPos (M := M))) : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
  (by
    litex_complete =>
      exact (
        (Litex.inNPos_positive _value_i4 h_107)
      )
  )

theorem h_109 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.Z (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_107 : Litex.In _value_i4 (Litex.NPos (M := M))) : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 (h_108 (M := M) (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_105 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_107))
      )
  )

theorem h_110 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.Z (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_107 : Litex.In _value_i4 (Litex.NPos (M := M))) : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 (h_108 (M := M) (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_105 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_107)) _litex_zero.symm)
      )
  )

noncomputable def _object_w18 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.Z (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_107 : Litex.In _value_i4 (Litex.NPos (M := M))) := (let _wd_1_0 := (let _wd_2_0 := _value_i4;
let _wd_2_1 := (Litex.quot _value_i3 _wd_2_0 h_105 h_107);
(Litex.mul _wd_2_0 _wd_2_1 (Litex.naturalToComplex _wd_2_0 (Litex.inNPos_natural _wd_2_0 h_107)) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.quotInZ _atomic_wd_1_0)))));
let _wd_1_1 := (Litex.mod _value_i3 _value_i4 h_105 (Litex.naturalToInteger _value_i4 (Litex.inNPos_natural _value_i4 h_107)) (h_110 (M := M) (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_105 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_107));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.mulInC _value_i4 (_atomic_wd_1_0).val.right (Litex.naturalToComplex _value_i4 (Litex.inNPos_natural _value_i4 h_107)) (Litex.integerToComplex (_atomic_wd_1_0).val.right (Litex.quotInZ (_atomic_wd_1_0).val.right)))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.modInZ _atomic_wd_1_0)))))

theorem h_111 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.Z (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_107 : Litex.In _value_i4 (Litex.NPos (M := M))) : (by
  let _equal_wd_1_1 := (_object_w18 (M := M) (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_105 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_107)
  exact Litex.Same _value_i3 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_1 := (_object_w18 (M := M) (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_105 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_107);
        (show Litex.Same _value_i3 _equal_wd_1_1 from (Litex.quotDecomposition ((_equal_wd_1_1).val.left).val.right false)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_integer_x5f_division_x2f_statement_x2e_lit
