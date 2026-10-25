import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_collection_x5f_cardinality_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (let _wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.finiteSetSize _wd_1_0 (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0))))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (2 : ℂ) (let _stat := _equal_wd_1_0;
        let _finite_tail_0 := _stat.val.set;
        let _finite_tail_1 := _finite_tail_0.val.tail;
        let _finite_tail_2 := _finite_tail_1.val.tail;
        have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
        have _card_2 : Litex.finiteCard (Litex.denote _finite_tail_2) = 0 := Litex.finiteCardEmpty;
        have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
        have _card_1 : Litex.finiteCard (Litex.denote _finite_tail_1) = 1 := (Litex.finiteCardInsert _finite_tail_1 _finite_2).trans (congrArg (fun n : ℕ => n + 1) _card_2);
        have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
        have _card_0 : Litex.finiteCard (Litex.denote _finite_tail_0) = 2 := (Litex.finiteCardInsert _finite_tail_0 _finite_1).trans (congrArg (fun n : ℕ => n + 1) _card_1);
        (Litex.finiteSetSizeDenote _stat 2 _card_0).trans (congrArg M.number (by norm_num : ((2 : ℕ) : ℂ) = (2 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0);
(Litex.finiteSetSize _wd_1_0 (by
  let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
  _finite_0))))

theorem h_7 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (let _stat := _equal_wd_1_0;
        let _finite_tail_0 := _stat.val.set;
        have _finite_0 : Litex.IsFiniteSet _finite_tail_0 := Litex.finiteSetEmpty;
        have _card_0 : Litex.finiteCard (Litex.denote _finite_tail_0) = 0 := Litex.finiteCardEmpty;
        (Litex.finiteSetSizeDenote _stat 0 _card_0).trans (congrArg M.number (by norm_num : ((0 : ℕ) : ℂ) = (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w5 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.finiteSetSize _wd_2_0 (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  let _finite_tail_3 := _finite_tail_2.val.tail;
  have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
  have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0))));
let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.finiteSetSize _wd_2_0 (by
    let _atomic_wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
      let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
      let _setTail_3 := Litex.emptySet (M := M);
      let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
      let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0)
    exact (let _finite_tail_0 := _atomic_wd_2_0;
    let _finite_tail_1 := _finite_tail_0.val.tail;
    let _finite_tail_2 := _finite_tail_1.val.tail;
    let _finite_tail_3 := _finite_tail_2.val.tail;
    have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
    have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
    have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
    _finite_0))))
  exact (Litex.naturalToComplex _atomic_wd_1_0 (Litex.finiteSetSizeInN _atomic_wd_1_0))) (Litex.numberInC (M := M) (1 : ℂ))))

theorem h_14 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (4 : ℂ)) ((3 : ℂ) + (1 : ℂ)) (4 : ℂ) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _stat := (_equal_wd_1_0).val.left;
        let _finite_tail_0 := _stat.val.set;
        let _finite_tail_1 := _finite_tail_0.val.tail;
        let _finite_tail_2 := _finite_tail_1.val.tail;
        let _finite_tail_3 := _finite_tail_2.val.tail;
        have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
        have _card_3 : Litex.finiteCard (Litex.denote _finite_tail_3) = 0 := Litex.finiteCardEmpty;
        have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
        have _card_2 : Litex.finiteCard (Litex.denote _finite_tail_2) = 1 := (Litex.finiteCardInsert _finite_tail_2 _finite_3).trans (congrArg (fun n : ℕ => n + 1) _card_3);
        have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
        have _card_1 : Litex.finiteCard (Litex.denote _finite_tail_1) = 2 := (Litex.finiteCardInsert _finite_tail_1 _finite_2).trans (congrArg (fun n : ℕ => n + 1) _card_2);
        have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
        have _card_0 : Litex.finiteCard (Litex.denote _finite_tail_0) = 3 := (Litex.finiteCardInsert _finite_tail_0 _finite_1).trans (congrArg (fun n : ℕ => n + 1) _card_1);
        (Litex.finiteSetSizeDenote _stat 3 _card_0).trans (congrArg M.number (by norm_num : ((3 : ℕ) : ℂ) = (3 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (by norm_num))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_collection_x5f_cardinality_x2f_statement_x2e_lit
