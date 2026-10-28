import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_homogeneous_x5f_cartesian_x5f_carriers_x2f_statement_x2e_lit

universe u v1 v4 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsSet _value_i1), (by
  let _object_w1 := (Litex.finiteSeq _value_i1 (Litex.number (M := M) (3 : ℂ)) h_6 (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
  let _object_w2 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i1, Litex.denote _value_i1] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i1) (fun i => Fin.elim0 i)))))
  let _object_w3 := (Litex.finiteSeq _value_i1 (Litex.number (M := M) (1 : ℂ)) h_6 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
  let _object_w4 := (Litex.cart (M := M) ![Litex.denote _value_i1] (Fin.cases (Litex.isSet _value_i1) (fun i => Fin.elim0 i)))
  let _object_w5 := (Litex.finiteSeq _value_i1 (Litex.number (M := M) (0 : ℂ)) h_6 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
  let _object_w6 := (Litex.cart (M := M) ![] (fun i => Fin.elim0 i))
  exact (((by
    let _equal_wd_1_0 := _object_w1
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w1
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w3
    let _equal_wd_1_1 := _object_w4
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6
          let _object_w1 := (Litex.finiteSeq _value_i1 (Litex.number (M := M) (3 : ℂ)) h_6 (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
          let _object_w2 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i1, Litex.denote _value_i1] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i1) (fun i => Fin.elim0 i)))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w1
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w1;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((by
                    let _cart := _equal_wd_1_1
                    let _seq := _equal_wd_1_0
                    have _source_length : Litex.Same _seq.val.length (Litex.number (3 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                    have _length : Litex.Same _seq.val.length (Litex.number ((3 : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))
                    have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by
                      intro i
                      fin_cases i
                      · exact (show @Eq M.Value _ _ from Eq.refl _)
                      · exact (show @Eq M.Value _ _ from Eq.refl _)
                      · exact (show @Eq M.Value _ _ from Eq.refl _)
                    change Litex.denote _cart = Litex.denote _seq
                    rw [Litex.denoteFiniteSeq _seq 3 _length]
                    apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))
                    intro p
                    change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _
                    rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]
                    constructor
                    · exact And.left
                    · intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)
                  ) : Litex.Same _equal_wd_1_1 _equal_wd_1_0)).symm))
                )
            )
          have h_2 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w1
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (h_1).symm
                )
            )
          let _object_w3 := (Litex.finiteSeq _value_i1 (Litex.number (M := M) (1 : ℂ)) h_6 (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))
          let _object_w4 := (Litex.cart (M := M) ![Litex.denote _value_i1] (Fin.cases (Litex.isSet _value_i1) (fun i => Fin.elim0 i)))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w3
            let _equal_wd_1_1 := _object_w4
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((by
                    let _cart := _equal_wd_1_1
                    let _seq := _equal_wd_1_0
                    have _source_length : Litex.Same _seq.val.length (Litex.number (1 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                    have _length : Litex.Same _seq.val.length (Litex.number ((1 : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))
                    have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by
                      intro i
                      fin_cases i
                      · exact (show @Eq M.Value _ _ from Eq.refl _)
                    change Litex.denote _cart = Litex.denote _seq
                    rw [Litex.denoteFiniteSeq _seq 1 _length]
                    apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))
                    intro p
                    change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _
                    rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]
                    constructor
                    · exact And.left
                    · intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)
                  ) : Litex.Same _equal_wd_1_1 _equal_wd_1_0)).symm))
                )
            )
          let _object_w5 := (Litex.finiteSeq _value_i1 (Litex.number (M := M) (0 : ℂ)) h_6 (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))
          let _object_w6 := (Litex.cart (M := M) ![] (fun i => Fin.elim0 i))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((by
                    let _cart := _equal_wd_1_1
                    let _seq := _equal_wd_1_0
                    have _source_length : Litex.Same _seq.val.length (Litex.number (0 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                    have _length : Litex.Same _seq.val.length (Litex.number ((0 : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))
                    have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by
                      intro i
                      fin_cases i
                    change Litex.denote _cart = Litex.denote _seq
                    rw [Litex.denoteFiniteSeq _seq 0 _length]
                    apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))
                    intro p
                    change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _
                    rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]
                    constructor
                    · exact And.left
                    · intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)
                  ) : Litex.Same _equal_wd_1_1 _equal_wd_1_0)).symm))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 h_4)))
        )
      )
  )

noncomputable def _object_i2 := (Litex.R (M := M))
theorem h_39 : Litex.IsSet (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.isSet (Litex.R (M := M)))
      )
  )
theorem h_40 : Litex.Same (_object_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.R (M := M)))
      )
  )

noncomputable def _object_i3 := (Litex.number (M := M) (3 : ℂ))
theorem h_44 : Litex.In (_object_i3 (M := M)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))
      )
  )
theorem h_45 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.naturalNonnegative (_object_i3 (M := M)) (h_44 (M := M)))
      )
  )
theorem h_46 : Litex.Same (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))
      )
  )

noncomputable def _object_w13 := (Litex.cart (M := M) ![Litex.denote (_object_i2 (M := M)), Litex.denote (Litex.R (M := M)), Litex.denote (_object_i2 (M := M))] (Fin.cases (Litex.isSet (_object_i2 (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (_object_i2 (M := M))) (fun i => Fin.elim0 i)))))

noncomputable def _object_w14 := (Litex.finiteSeq (Litex.R (M := M)) (_object_i3 (M := M)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (h_44 (M := M)))

theorem h_47 : (by
  let _equal_wd_1_0 := (_object_w13 (M := M))
  let _equal_wd_1_1 := (_object_w14 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w13 (M := M));
        let _equal_wd_1_1 := (_object_w14 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((by
          let _cart := _equal_wd_1_0
          let _seq := _equal_wd_1_1
          have _source_length : Litex.Same _seq.val.length (Litex.number (3 : ℂ)) := (h_46 (M := M))
          have _length : Litex.Same _seq.val.length (Litex.number ((3 : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))
          have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by
            intro i
            fin_cases i
            · exact (h_40 (M := M))
            · exact (show @Eq M.Value _ _ from Eq.refl _)
            · exact (h_40 (M := M))
          change Litex.denote _cart = Litex.denote _seq
          rw [Litex.denoteFiniteSeq _seq 3 _length]
          apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))
          intro p
          change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _
          rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]
          constructor
          · exact And.left
          · intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)
        ) : Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
      )
  )

theorem h_66 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_80 : Litex.In _value_i4 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))), (by
  let _object_w19 := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M))))
  exact (by
    let _atomic_wd_1_1 := _object_w19
    exact Litex.In _value_i4 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_80
          let _object_h81 := (Litex.cartCall _value_i4 _ (Litex.number (M := M) (1 : ℂ)) h_80 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 3); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 3))))
          have h_81 : Litex.In _object_h81 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_80 (0 : Fin 3) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h82 := (Litex.cartCall _value_i4 _ (Litex.number (M := M) (2 : ℂ)) h_80 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 3); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 3))))
          have h_82 : Litex.In _object_h82 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_80 (1 : Fin 3) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h83 := (Litex.cartCall _value_i4 _ (Litex.number (M := M) (3 : ℂ)) h_80 (by change M.mem (M.number (3 : ℂ)) (Litex.FiniteFunction.indexSet 3); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (2 : Fin 3))))
          have h_83 : Litex.In _object_h83 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_80 (2 : Fin 3) (3 : ℂ) (by norm_num))
                )
            )
          let _object_w19 := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M))))
          have h_65 : (by
            let _atomic_wd_1_1 := _object_w19
            exact Litex.In _value_i4 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w19
                    exact (Litex.inOfSame _value_i4 _value_i4 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) _atomic_wd_1_1 (Eq.refl _) (((by
                      let _cart := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                      let _seq := _atomic_wd_1_1
                      have _source_length : Litex.Same _seq.val.length (Litex.number (3 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                      have _length : Litex.Same _seq.val.length (Litex.number ((3 : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))
                      have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by
                        intro i
                        fin_cases i
                        · exact (show @Eq M.Value _ _ from Eq.refl _)
                        · exact (show @Eq M.Value _ _ from Eq.refl _)
                        · exact (show @Eq M.Value _ _ from Eq.refl _)
                      change Litex.denote _cart = Litex.denote _seq
                      rw [Litex.denoteFiniteSeq _seq 3 _length]
                      apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))
                      intro p
                      change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _
                      rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]
                      constructor
                      · exact And.left
                      · intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)
                    ) : Litex.Same (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) _atomic_wd_1_1)) (h_80)))
                )
            )
          let _object_h135 := (Litex.fnSet (Litex.finiteSeqSignature _object_w19))
          have h_135 : Litex.In _value_i4 _object_h135 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 _object_w19 _object_h135 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet _object_w19) h_65)
                )
            )
          exact h_65
        )
      )
  )

theorem h_137 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_207 : Litex.In _value_i6 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M))))), (by
  let _object_w23 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (by
    let _atomic_wd_1_1 := _object_w23
    exact Litex.In _value_i6 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_207
          let _object_h208 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M))))))
          have h_208 : Litex.In _value_i6 _object_h208 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i6 _value_i6 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M)))) _object_h208 (Litex.sameRefl _value_i6) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M))))) h_207)
                )
            )
          let _object_w23 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
          have h_136 : (by
            let _atomic_wd_1_1 := _object_w23
            exact Litex.In _value_i6 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w23
                    exact (Litex.inOfSame _value_i6 _value_i6 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M)))) _atomic_wd_1_1 (Eq.refl _) ((((by
                      let _cart := _atomic_wd_1_1
                      let _seq := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M))))
                      have _source_length : Litex.Same _seq.val.length (Litex.number (3 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
                      have _length : Litex.Same _seq.val.length (Litex.number ((3 : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))
                      have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by
                        intro i
                        fin_cases i
                        · exact (show @Eq M.Value _ _ from Eq.refl _)
                        · exact (show @Eq M.Value _ _ from Eq.refl _)
                        · exact (show @Eq M.Value _ _ from Eq.refl _)
                      change Litex.denote _cart = Litex.denote _seq
                      rw [Litex.denoteFiniteSeq _seq 3 _length]
                      apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))
                      intro p
                      change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _
                      rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]
                      constructor
                      · exact And.left
                      · intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)
                    ) : Litex.Same _atomic_wd_1_1 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M)))))).symm) (h_207)))
                )
            )
          let _object_h240 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (1 : ℂ)) h_136 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 3); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 3))))
          have h_240 : Litex.In _object_h240 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_136 (0 : Fin 3) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h241 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (2 : ℂ)) h_136 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 3); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 3))))
          have h_241 : Litex.In _object_h241 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_136 (1 : Fin 3) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h242 := (Litex.cartCall _value_i6 _ (Litex.number (M := M) (3 : ℂ)) h_136 (by change M.mem (M.number (3 : ℂ)) (Litex.FiniteFunction.indexSet 3); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (2 : Fin 3))))
          have h_242 : Litex.In _object_h242 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_136 (2 : Fin 3) (3 : ℂ) (by norm_num))
                )
            )
          exact h_136
        )
      )
  )

noncomputable def _object_w27 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))

noncomputable def _object_w28 := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSetOfSame (_object_i2 (M := M)) (Litex.R (M := M)) (h_40 (M := M)) (h_39 (M := M))) (Litex.inOfSame (_object_i3 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.N (M := M)) (Litex.N (M := M)) (h_46 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_44 (M := M))))

theorem h_243 : (by
  let _atomic_wd_1_0 := (_object_w27 (M := M))
  let _atomic_wd_1_1 := (_object_w28 (M := M))
  exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w27 (M := M))
          let _atomic_wd_1_1 := (_object_w28 (M := M))
          exact (Litex.subsetOfSame _atomic_wd_1_0 _atomic_wd_1_0 _atomic_wd_1_0 _atomic_wd_1_1 (Eq.refl _) (((by
            let _cart := _atomic_wd_1_0
            let _seq := _atomic_wd_1_1
            have _source_length : Litex.Same _seq.val.length (Litex.number (3 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
            have _length : Litex.Same _seq.val.length (Litex.number ((3 : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))
            have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by
              intro i
              fin_cases i
              · exact (show @Eq M.Value _ _ from Eq.refl _)
              · exact (show @Eq M.Value _ _ from Eq.refl _)
              · exact (show @Eq M.Value _ _ from Eq.refl _)
            change Litex.denote _cart = Litex.denote _seq
            rw [Litex.denoteFiniteSeq _seq 3 _length]
            apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))
            intro p
            change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _
            rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]
            constructor
            · exact And.left
            · intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)
          ) : Litex.Same _atomic_wd_1_0 _atomic_wd_1_1)) (Litex.subsetRefl _atomic_wd_1_0)))
      )
  )

theorem h_264 : (by
  let _atomic_wd_1_0 := (_object_w28 (M := M))
  let _atomic_wd_1_1 := (_object_w27 (M := M))
  exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w28 (M := M))
          let _atomic_wd_1_1 := (_object_w27 (M := M))
          exact (Litex.subsetOfSame _atomic_wd_1_0 _atomic_wd_1_0 _atomic_wd_1_0 _atomic_wd_1_1 (Eq.refl _) ((((by
            let _cart := _atomic_wd_1_1
            let _seq := _atomic_wd_1_0
            have _source_length : Litex.Same _seq.val.length (Litex.number (3 : ℂ)) := (show @Eq M.Value _ _ from Eq.refl _)
            have _length : Litex.Same _seq.val.length (Litex.number ((3 : ℕ) : ℂ)) := _source_length.trans (congrArg M.number (by norm_num))
            have _factors : ∀ i, _cart.val.factors i = Litex.denote _seq.val.carrier := by
              intro i
              fin_cases i
              · exact (show @Eq M.Value _ _ from Eq.refl _)
              · exact (show @Eq M.Value _ _ from Eq.refl _)
              · exact (show @Eq M.Value _ _ from Eq.refl _)
            change Litex.denote _cart = Litex.denote _seq
            rw [Litex.denoteFiniteSeq _seq 3 _length]
            apply Litex.SetSemantics.ext _ _ (Litex.isSet _cart) (Litex.FunctionSemantics.fnSet_isSet _ _ (Litex.FiniteFunction.indexSet_isSet _) (Litex.isSet _seq.val.carrier))
            intro p
            change M.mem p (Litex.FiniteFunction.cartValue _cart.val.factors) ↔ _
            rw [Litex.cartMembersWithReturnBound _cart.val.factors (Litex.denote _seq.val.carrier) (fun i x hx => _factors i ▸ hx) p]
            constructor
            · exact And.left
            · intro hp; refine ⟨hp, ?_⟩; intro i; rw [_factors i]; exact Litex.FunctionSemantics.call_mem _ _ _ _ hp (Litex.FiniteFunction.index_mem i)
          ) : Litex.Same _atomic_wd_1_1 _atomic_wd_1_0)).symm) (Litex.subsetRefl _atomic_wd_1_0)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_homogeneous_x5f_cartesian_x5f_carriers_x2f_statement_x2e_lit
