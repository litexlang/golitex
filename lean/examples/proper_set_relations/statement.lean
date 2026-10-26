import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_proper_x5f_set_x5f_relations_x2f_statement_x2e_lit

universe u v2 v3 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
  exact Litex.ProperSubset _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
          exact (And.intro (by
            let _atomic_wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
            exact (by
              let _set := _atomic_wd_2_0
              exact (Litex.insertSubset _set.val.element _set.val.tail _atomic_wd_2_1 _set.wd (by
              let _atomic_wd_3_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
              exact (by
                let _set := _atomic_wd_3_1
                exact ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail _atomic_wd_2_1 _set.val.tail.wd (by
              let _atomic_wd_3_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
              exact (by
                let _set := _atomic_wd_3_1
                exact ((Litex.inInsert_iff (Litex.number (M := M) (2 : ℂ)) _set.val.element _set.val.tail _set.wd).mpr (Or.inr ((Litex.inInsert_iff (Litex.number (M := M) (2 : ℂ)) _set.val.tail.val.element _set.val.tail.val.tail _set.val.tail.wd).mpr (Or.inl (show @Eq M.Value _ _ from Eq.refl _))))))) (Litex.emptySubset _atomic_wd_2_1))))) (by
            let _atomic_wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            let _atomic_wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
            exact (let _left := _atomic_wd_2_0;
            let _right := _atomic_wd_2_1;
            have _left_card : Litex.finiteCard (Litex.denote _left) = 2 := (let _finite_tail_0 := _left;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            let _finite_tail_2 := _finite_tail_1.val.tail;
            have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
            have _card_2 : Litex.finiteCard (Litex.denote _finite_tail_2) = 0 := Litex.finiteCardEmpty;
            have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
            have _card_1 : Litex.finiteCard (Litex.denote _finite_tail_1) = 1 := (Litex.finiteCardInsert _finite_tail_1 _finite_2).trans (congrArg (fun n : ℕ => n + 1) _card_2);
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            have _card_0 : Litex.finiteCard (Litex.denote _finite_tail_0) = 2 := (Litex.finiteCardInsert _finite_tail_0 _finite_1).trans (congrArg (fun n : ℕ => n + 1) _card_1);
            _card_0);
            have _right_card : Litex.finiteCard (Litex.denote _right) = 3 := (let _finite_tail_0 := _right;
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
            _card_0);
            fun h => (by decide : (2 : ℕ) ≠ 3) (_left_card.symm.trans ((congrArg (Litex.finiteCard (M := M)) h).trans _right_card))))))
      )
  )

theorem h_49 : Litex.Subset (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        ((h_1 (M := M))).1
      )
  )

theorem h_50 : ¬ Litex.Same (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        ((h_1 (M := M))).2
      )
  )

theorem h_51 : (by
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
  let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact Litex.ProperSuperset _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
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
          let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          exact (And.intro (by
            let _atomic_wd_2_0 := _atomic_wd_1_1
            let _atomic_wd_2_1 := _atomic_wd_1_0
            exact (h_49 (M := M))) (by
            let _atomic_wd_2_0 := _atomic_wd_1_0
            let _atomic_wd_2_1 := _atomic_wd_1_1
            exact (fun _litex_same => (h_50 (M := M)) _litex_same.symm))))
      )
  )

theorem h_69 : Litex.Subset (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        ((h_51 (M := M))).1
      )
  )

theorem h_70 : ¬ Litex.Same (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        ((h_51 (M := M))).2
      )
  )

theorem h_71 : Litex.Superset (Litex.R (M := M)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.N (M := M)) (Litex.R (M := M)) (fun _a _ha => (Litex.naturalToReal _a _ha)))
      )
  )

theorem h_77 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_78 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_79 : Litex.IsSet _value_i3) (h_74 : Litex.ProperSubset _value_i2 _value_i3), ((Litex.Subset _value_i2 _value_i3) ∧ (¬ Litex.Same _value_i2 _value_i3)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_78 _Host_i3 _rep_i3 _value_i3 h_79 h_74
          have h_81 : Litex.Subset _value_i2 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (h_74).1
                )
            )
          have h_82 : ¬ Litex.Same _value_i2 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (h_74).2
                )
            )
          have h_87 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_78
                )
            )
          have h_88 : Litex.IsSet _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  h_79
                )
            )
          have h_90 : Litex.Subset _value_i2 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (h_74).1
                )
            )
          have h_91 : ¬ Litex.Same _value_i2 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (h_74).2
                )
            )
          exact (And.intro h_90 h_91)
        )
      )
  )

theorem h_109 : (by
  let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
  exact Litex.Subset _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_110 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          have h_111 : (by
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
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
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
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          have h_112 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
              let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
            exact Litex.ProperSubset _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                      let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_2 := Litex.emptySet (M := M);
                      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
                    exact (h_1 (M := M)))
                )
            )
          have h_123 : Litex.Subset (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
            let _setTail_3 := Litex.emptySet (M := M);
            let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
            let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (h_112).1
                )
            )
          have h_124 : ¬ Litex.Same (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
            let _setTail_3 := Litex.emptySet (M := M);
            let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
            let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (h_112).2
                )
            )
          have h_113 : Litex.Subset (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
            let _setTail_3 := Litex.emptySet (M := M);
            let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
            let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (And.left ((h_77 (M := M)) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_2 := Litex.emptySet (M := M);
                    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_110 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                    let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
                    let _setTail_3 := Litex.emptySet (M := M);
                    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_111 h_112))
                )
            )
          have h_114 : ¬ Litex.Same (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
            let _setTail_3 := Litex.emptySet (M := M);
            let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
            let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (And.right ((h_77 (M := M)) (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_2 := Litex.emptySet (M := M);
                    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
                    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_110 (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
                    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
                    let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
                    let _setTail_3 := Litex.emptySet (M := M);
                    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
                    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
                    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
                    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_111 h_112))
                )
            )
          exact (by
          let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
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
          exact h_113)
        )
      )
  )

theorem h_142 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_144 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_145 : Litex.IsSet _value_i8) (h_139 : Litex.ProperSuperset _value_i7 _value_i8), ((Litex.Subset _value_i8 _value_i7) ∧ (¬ Litex.Same _value_i7 _value_i8)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_144 _Host_i8 _rep_i8 _value_i8 h_145 h_139
          have h_147 : Litex.Subset _value_i8 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (h_139).1
                )
            )
          have h_148 : ¬ Litex.Same _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (h_139).2
                )
            )
          have h_140 : Litex.Subset _value_i8 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  h_147
                )
            )
          have h_141 : ¬ Litex.Same _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  h_148
                )
            )
          exact (And.intro h_140 h_141)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_proper_x5f_set_x5f_relations_x2f_statement_x2e_lit
