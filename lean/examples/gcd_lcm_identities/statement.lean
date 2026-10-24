import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_gcd_x5f_lcm_x5f_identities_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_21 : Litex.In _value_i1 (Litex.Z (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_22 : Litex.In _value_i2 (Litex.Z (M := M))) (h_3 : ((¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))))), (by
  let _object_w4 := (Litex.gcd _value_i1 _value_i2 h_21 h_22 h_3)
  have h_4 : (by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.gcdInNPos _atomic_wd_1_0))
        )
    )
  let _object_w7 := (Litex.gcd _value_i2 _value_i1 h_22 h_21 (Or.symm h_3))
  let _object_w8 := (let _wd_1_0 := (Litex.lcm _value_i1 _value_i2 h_21 h_22);
  let _wd_1_1 := _object_w4;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.lcmInN _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _object_w4
    exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 h_4)))))
  let _object_w9 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_21) (Litex.integerToComplex _value_i2 h_22));
  (Litex.abs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR _value_i1 _value_i2 (Litex.integerToReal _value_i1 h_21) (Litex.integerToReal _value_i2 h_22)))))
  let _object_w10 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := _object_w4;
  (Litex.mod _wd_1_0 _wd_1_1 h_21 (by
    let _atomic_wd_1_0 := _object_w4
    exact (Litex.naturalToInteger _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 h_4))) (Litex.gcdNonzero _wd_1_1)))
  exact (((by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M)))) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _atomic_wd_1_0 := _object_w10
    exact Litex.IsSet _atomic_wd_1_0)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_21 _Host_i2 _rep_i2 _value_i2 h_22 h_3
          let _object_w4 := (Litex.gcd _value_i1 _value_i2 h_21 h_22 h_3)
          have h_4 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (Litex.gcdInNPos _atomic_wd_1_0))
                )
            )
          have h_801 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _object_w4 h_4)
                )
            )
          have h_802 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_w4 h_801)
                )
            )
          have h_803 : ¬ Litex.Same _object_w4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w4 h_801) _litex_zero.symm)
                )
            )
          let _object_w7 := (Litex.gcd _value_i2 _value_i1 h_22 h_21 (Or.symm h_3))
          have h_5 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.gcdCommutative _equal_wd_1_0)))
                )
            )
          let _object_w8 := (let _wd_1_0 := (Litex.lcm _value_i1 _value_i2 h_21 h_22);
          let _wd_1_1 := _object_w4;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.lcmInN _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 h_4)))))
          let _object_w9 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (Litex.integerToComplex _value_i1 h_21) (Litex.integerToComplex _value_i2 h_22));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR _value_i1 _value_i2 (Litex.integerToReal _value_i1 h_21) (Litex.integerToReal _value_i2 h_22)))))
          have h_6 : (by
            let _equal_wd_1_0 := _object_w8
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w8;
                  let _equal_wd_1_1 := _object_w9;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.gcdLcmProduct (_equal_wd_1_0).val.right false false)))
                )
            )
          let _object_w10 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := _object_w4;
          (Litex.mod _wd_1_0 _wd_1_1 h_21 (by
            let _atomic_wd_1_0 := _object_w4
            exact (Litex.naturalToInteger _atomic_wd_1_0 (Litex.inNPos_natural _atomic_wd_1_0 h_4))) (Litex.gcdNonzero _wd_1_1)))
          have h_7 : (by
            let _atomic_wd_1_0 := _object_w10
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          exact (And.intro h_4 (And.intro h_5 (And.intro h_6 h_7)))
        )
      )
  )

theorem h_3046 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3059 : Litex.In _value_i3 (Litex.Z (M := M))) (h_3042 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w13 := (Litex.gcd _value_i3 (Litex.number (M := M) (0 : ℂ)) h_3059 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (by
    classical
    apply Classical.byContradiction
    intro _negative_disjunction
    have h_3376 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
          )
      )
    exact _negative_disjunction (Or.inl h_3042)
  ))
  let _object_w14 := (Litex.abs _value_i3 (Litex.integerToReal _value_i3 h_3059))
  let _object_w15 := (Litex.gcd (Litex.number (M := M) (0 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) h_3059 (by
    classical
    apply Classical.byContradiction
    intro _negative_disjunction
    have h_3715 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
          )
      )
    exact _negative_disjunction (Or.inl (Litex.notSameOfSame _value_i3 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_3715 (show @Eq M.Value _ _ from Eq.refl _) h_3042))
  ))
  let _object_w16 := (Litex.gcd _value_i3 _value_i3 h_3059 h_3059 (by
    classical
    apply Classical.byContradiction
    intro _negative_disjunction
    have h_4208 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
          )
      )
    exact _negative_disjunction (Or.inl h_3042)
  ))
  exact (((by
    let _equal_wd_1_0 := _object_w13
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w15
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w16
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_3059 h_3042
          let _object_w13 := (Litex.gcd _value_i3 (Litex.number (M := M) (0 : ℂ)) h_3059 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (by
            classical
            apply Classical.byContradiction
            intro _negative_disjunction
            have h_3376 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
                  )
              )
            exact _negative_disjunction (Or.inl h_3042)
          ))
          let _object_w14 := (Litex.abs _value_i3 (Litex.integerToReal _value_i3 h_3059))
          have h_3043 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w13;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.gcdRightZeroAbs _equal_wd_1_0 (Litex.sameRefl (Litex.number (M := M) 0)) h_3042)))
                )
            )
          let _object_w15 := (Litex.gcd (Litex.number (M := M) (0 : ℂ)) _value_i3 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) h_3059 (by
            classical
            apply Classical.byContradiction
            intro _negative_disjunction
            have h_3715 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
                  )
              )
            exact _negative_disjunction (Or.inl (Litex.notSameOfSame _value_i3 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) h_3715 (show @Eq M.Value _ _ from Eq.refl _) h_3042))
          ))
          have h_3044 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w15;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.gcdLeftZeroAbs _equal_wd_1_0 (Litex.sameRefl (Litex.number (M := M) 0)) h_3042)))
                )
            )
          let _object_w16 := (Litex.gcd _value_i3 _value_i3 h_3059 h_3059 (by
            classical
            apply Classical.byContradiction
            intro _negative_disjunction
            have h_4208 : Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
                  )
              )
            exact _negative_disjunction (Or.inl h_3042)
          ))
          have h_3045 : (by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w16;
                  let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _intop := _equal_wd_1_0
                    exact (Litex.gcdSelfAbs _intop (Litex.sameRefl _intop.val.left))
                  )))
                )
            )
          exact (And.intro h_3043 (And.intro h_3044 h_3045))
        )
      )
  )

theorem h_4217 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_4230 : Litex.In _value_i4 (Litex.Z (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_4231 : Litex.In _value_i5 (Litex.Z (M := M))), (by
  let _object_w18 := (Litex.lcm _value_i4 _value_i5 h_4230 h_4231)
  let _object_w19 := (Litex.lcm _value_i5 _value_i4 h_4231 h_4230)
  let _object_w20 := (Litex.lcm _value_i4 _value_i4 h_4230 h_4230)
  let _object_w21 := (Litex.abs _value_i4 (Litex.integerToReal _value_i4 h_4230))
  exact (((by
    let _equal_wd_1_0 := _object_w18
    let _equal_wd_1_1 := _object_w19
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w20
    let _equal_wd_1_1 := _object_w21
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_4230 _Host_i5 _rep_i5 _value_i5 h_4231
          let _object_w18 := (Litex.lcm _value_i4 _value_i5 h_4230 h_4231)
          let _object_w19 := (Litex.lcm _value_i5 _value_i4 h_4231 h_4230)
          have h_4215 : (by
            let _equal_wd_1_0 := _object_w18
            let _equal_wd_1_1 := _object_w19
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w18;
                  let _equal_wd_1_1 := _object_w19;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.lcmCommutative _equal_wd_1_0)))
                )
            )
          let _object_w20 := (Litex.lcm _value_i4 _value_i4 h_4230 h_4230)
          let _object_w21 := (Litex.abs _value_i4 (Litex.integerToReal _value_i4 h_4230))
          have h_4216 : (by
            let _equal_wd_1_0 := _object_w20
            let _equal_wd_1_1 := _object_w21
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w20;
                  let _equal_wd_1_1 := _object_w21;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _intop := _equal_wd_1_0
                    exact (Litex.lcmSelfAbs _intop (Litex.sameRefl _intop.val.left))
                  )))
                )
            )
          exact (And.intro h_4215 h_4216)
        )
      )
  )

theorem h_4291 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_4304 : Litex.In _value_i6 (Litex.Z (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_4305 : Litex.In _value_i7 (Litex.Z (M := M))) (h_4289 : ((¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ))))), (by
  let _object_w27 := (Litex.gcd _value_i6 _value_i7 h_4304 h_4305 (Or.symm h_4289))
  exact (by
    let _atomic_wd_1_0 := _object_w27
    exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_4304 _Host_i7 _rep_i7 _value_i7 h_4305 h_4289
          let _object_w27 := (Litex.gcd _value_i6 _value_i7 h_4304 h_4305 (Or.symm h_4289))
          have h_4290 : (by
            let _atomic_wd_1_0 := _object_w27
            exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w27
                    exact (Litex.gcdInNPos _atomic_wd_1_0))
                )
            )
          have h_5838 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _object_w27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _object_w27 h_4290)
                )
            )
          have h_5839 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _object_w27 h_5838)
                )
            )
          have h_5840 : ¬ Litex.Same _object_w27 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _object_w27 h_5838) _litex_zero.symm)
                )
            )
          exact h_4290
        )
      )
  )

theorem h_5842 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_5855 : Litex.In _value_i8 (Litex.Z (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_5856 : Litex.In _value_i9 (Litex.Z (M := M))), (by
  let _object_w31 := (Litex.lcm _value_i8 _value_i9 h_5855 h_5856)
  exact (by
    let _atomic_wd_1_0 := _object_w31
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_5855 _Host_i9 _rep_i9 _value_i9 h_5856
          let _object_w31 := (Litex.lcm _value_i8 _value_i9 h_5855 h_5856)
          have h_5841 : (by
            let _atomic_wd_1_0 := _object_w31
            exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w31
                    exact (Litex.lcmInN _atomic_wd_1_0))
                )
            )
          have h_5878 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w31 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _object_w31 h_5841)
                )
            )
          exact h_5841
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_gcd_x5f_lcm_x5f_identities_x2f_statement_x2e_lit
