import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_collection_x5f_extrema_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
let _wd_2_2 := (Litex.number (M := M) (7 : ℂ));
(let _setElement_0 := _wd_2_0;
  let _setElement_1 := _wd_2_1;
  let _setElement_2 := _wd_2_2;
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 _wd_2_2 (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_2_1 (- (3 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_2_2 (- (3 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0));
(Litex.finiteExtremum true _wd_1_0 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  let _wd_2_2 := (Litex.number (M := M) (7 : ℂ));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setElement_2 := _wd_2_2;
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 _wd_2_2 (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_1 (- (3 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_2 (- (3 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  let _finite_tail_3 := _finite_tail_2.val.tail;
  have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
  have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  let _wd_2_2 := (Litex.number (M := M) (7 : ℂ));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setElement_2 := _wd_2_2;
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 _wd_2_2 (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_1 (- (3 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_2 (- (3 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (Litex.insertNonempty _atomic_wd_1_0)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  let _wd_2_2 := (Litex.number (M := M) (7 : ℂ));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setElement_2 := _wd_2_2;
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 _wd_2_2 (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_1 (- (3 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_2 (- (3 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (by
    let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.R (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.tail.val.element _set.val.tail.val.tail.val.tail (Litex.R (M := M)) _set.val.tail.val.tail.wd (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M))))))))))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) (7 : ℂ) ((let _stat := _equal_wd_1_0;

        let _stat_tail_0 := _stat.val.set;
        let _stat_tail_1 := _stat_tail_0.val.tail;
        let _stat_tail_2 := _stat_tail_1.val.tail;
        let _stat_tail_3 := _stat_tail_2.val.tail;
        have _members_3 : ∀ x, M.mem x (Litex.denote _stat_tail_3) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty;
        have _number_2 : Litex.denote _stat_tail_2.val.element = M.number (((7 : ℝ) : ℝ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (((7 : ℝ) : ℝ) : ℂ)));
        have _members_2 := Litex.finiteMembersInsert _stat_tail_2 (M.number (((7 : ℝ) : ℝ) : ℂ)) [] _number_2 _members_3;
        have _number_1 : Litex.denote _stat_tail_1.val.element = M.number (((2 : ℝ) : ℝ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ)));
        have _members_1 := Litex.finiteMembersInsert _stat_tail_1 (M.number (((2 : ℝ) : ℝ) : ℂ)) [M.number (((7 : ℝ) : ℝ) : ℂ)] _number_1 _members_2;
        have _number_0 : Litex.denote _stat_tail_0.val.element = M.number (((-3 : ℝ) : ℝ) : ℂ) := ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (((-3 : ℝ) : ℝ) : ℂ)));
        have _members_0 := Litex.finiteMembersInsert _stat_tail_0 (M.number (((-3 : ℝ) : ℝ) : ℂ)) [M.number (((2 : ℝ) : ℝ) : ℂ), M.number (((7 : ℝ) : ℝ) : ℂ)] _number_0 _members_1;
        Litex.finiteExtremumListDenote _stat [(-3 : ℝ), (2 : ℝ), (7 : ℝ)] (7 : ℝ) _members_0 (by norm_num) (by norm_num)).trans (congrArg M.number (by norm_num : (((7 : ℝ) : ℝ) : ℂ) = (7 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (let _wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
let _wd_2_2 := (Litex.number (M := M) (7 : ℂ));
(let _setElement_0 := _wd_2_0;
  let _setElement_1 := _wd_2_1;
  let _setElement_2 := _wd_2_2;
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 _wd_2_2 (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_2_1 (- (3 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _wd_2_2 (- (3 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0));
(Litex.finiteExtremum false _wd_1_0 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  let _wd_2_2 := (Litex.number (M := M) (7 : ℂ));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setElement_2 := _wd_2_2;
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 _wd_2_2 (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_1 (- (3 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_2 (- (3 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  let _finite_tail_3 := _finite_tail_2.val.tail;
  have _finite_3 : Litex.IsFiniteSet _finite_tail_3 := Litex.finiteSetEmpty;
  have _finite_2 := Litex.finiteSetInsert _finite_tail_2 _finite_3;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  let _wd_2_2 := (Litex.number (M := M) (7 : ℂ));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setElement_2 := _wd_2_2;
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 _wd_2_2 (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_1 (- (3 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_2 (- (3 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (Litex.insertNonempty _atomic_wd_1_0)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  let _wd_2_2 := (Litex.number (M := M) (7 : ℂ));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setElement_2 := _wd_2_2;
    let _setTail_3 := Litex.emptySet (M := M);
    let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
    let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 _wd_2_2 (2 : ℂ) (7 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_1 (- (3 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _wd_2_2 (- (3 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))) (Litex.notInEmpty _setElement_0)));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (by
    let _atomic_wd_2_0 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (3 : ℂ)) (-3 : ℝ) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.R (M := M)) _set.val.tail.wd (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.insertSubset _set.val.tail.val.tail.val.element _set.val.tail.val.tail.val.tail (Litex.R (M := M)) _set.val.tail.val.tail.wd (Litex.NativeBridge.numberInROfEq (M := M) (7 : ℂ) (7 : ℝ) (by norm_num)) (Litex.emptySubset (Litex.R (M := M))))))))))

noncomputable def _object_w4 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))

theorem h_34 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  let _equal_wd_1_1 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        let _equal_wd_1_1 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (-3 : ℂ) (- (3 : ℂ)) ((let _stat := _equal_wd_1_0;

        let _stat_tail_0 := _stat.val.set;
        let _stat_tail_1 := _stat_tail_0.val.tail;
        let _stat_tail_2 := _stat_tail_1.val.tail;
        let _stat_tail_3 := _stat_tail_2.val.tail;
        have _members_3 : ∀ x, M.mem x (Litex.denote _stat_tail_3) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty;
        have _number_2 : Litex.denote _stat_tail_2.val.element = M.number (((7 : ℝ) : ℝ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (((7 : ℝ) : ℝ) : ℂ)));
        have _members_2 := Litex.finiteMembersInsert _stat_tail_2 (M.number (((7 : ℝ) : ℝ) : ℂ)) [] _number_2 _members_3;
        have _number_1 : Litex.denote _stat_tail_1.val.element = M.number (((2 : ℝ) : ℝ) : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ)));
        have _members_1 := Litex.finiteMembersInsert _stat_tail_1 (M.number (((2 : ℝ) : ℝ) : ℂ)) [M.number (((7 : ℝ) : ℝ) : ℂ)] _number_1 _members_2;
        have _number_0 : Litex.denote _stat_tail_0.val.element = M.number (((-3 : ℝ) : ℝ) : ℂ) := ((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = (((-3 : ℝ) : ℝ) : ℂ)));
        have _members_0 := Litex.finiteMembersInsert _stat_tail_0 (M.number (((-3 : ℝ) : ℝ) : ℂ)) [M.number (((2 : ℝ) : ℝ) : ℂ), M.number (((7 : ℝ) : ℝ) : ℂ)] _number_0 _members_1;
        Litex.finiteExtremumListDenote _stat [(-3 : ℝ), (2 : ℝ), (7 : ℝ)] (-3 : ℝ) _members_0 (by norm_num) (by norm_num)).trans (congrArg M.number (by norm_num : (((-3 : ℝ) : ℝ) : ℂ) = (-3 : ℂ)))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))))
      )
  )

noncomputable def _object_w5 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(let _setElement_0 := _wd_2_0;
  let _setElement_1 := _wd_2_1;
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    let _atomic_wd_1_1 := _wd_2_1
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0));
(Litex.finiteExtremum true _wd_1_0 (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (Litex.insertNonempty _atomic_wd_1_0)) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (3 : ℂ)) ((1 : ℂ) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.R (M := M)) _set.wd (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.R (M := M)) _set.val.tail.wd (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num)))) (Litex.emptySubset (Litex.R (M := M)))))))))

noncomputable def _object_w6 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_68 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  let _equal_wd_1_1 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        let _equal_wd_1_1 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (2 : ℂ)) ((let _stat := _equal_wd_1_0;

        let _stat_tail_0 := _stat.val.set;
        let _stat_tail_1 := _stat_tail_0.val.tail;
        let _stat_tail_2 := _stat_tail_1.val.tail;
        have _members_2 : ∀ x, M.mem x (Litex.denote _stat_tail_2) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty;
        have _number_1 : Litex.denote _stat_tail_1.val.element = M.number ((((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ)));
        have _members_1 := Litex.finiteMembersInsert _stat_tail_1 (M.number ((((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ)) [] _number_1 _members_2;
        have _number_0 : Litex.denote _stat_tail_0.val.element = M.number ((((1 : ℝ) / (3 : ℝ)) : ℝ) : ℂ) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((((1 : ℝ) / (3 : ℝ)) : ℝ) : ℂ)));
        have _members_0 := Litex.finiteMembersInsert _stat_tail_0 (M.number ((((1 : ℝ) / (3 : ℝ)) : ℝ) : ℂ)) [M.number ((((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ)] _number_0 _members_1;
        Litex.finiteExtremumListDenote _stat [((1 : ℝ) / (3 : ℝ)), ((1 : ℝ) / (2 : ℝ))] ((1 : ℝ) / (2 : ℝ)) _members_0 (by norm_num) (by norm_num)).trans (congrArg M.number (by norm_num : ((((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ) = ((1 : ℂ) / (2 : ℂ))))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_collection_x5f_extrema_x2f_statement_x2e_lit
