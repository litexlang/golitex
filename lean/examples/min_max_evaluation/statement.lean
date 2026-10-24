import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_min_x5f_max_x5f_evaluation_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_w1 := (Litex.min (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (3 : ℂ) (let _extremum := _equal_wd_1_0;
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (Litex.max (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (5 : ℂ) (5 : ℝ) (by norm_num)))

theorem h_5 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (5 : ℂ) (let _extremum := _equal_wd_1_0;
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w5 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_1_1 := (Litex.number (M := M) (0.5 : ℂ));
(Litex.min _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (0.5 : ℂ) (0.5 : ℝ) (by norm_num))))

noncomputable def _object_w6 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_9 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  let _equal_wd_1_1 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        let _equal_wd_1_1 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((Min.min ((1 : ℝ) / (3 : ℝ)) ((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ) ((1 : ℂ) / (3 : ℂ)) (let _extremum := _equal_wd_1_0;
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum ((1 : ℝ) / (3 : ℝ)) ((1 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2.1 ((_equal_wd_1_0).val.left).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((((1 : ℝ) / (3 : ℝ)) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (0.5 : ℂ))).trans (congrArg M.number (by norm_num : (0.5 : ℂ) = ((((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))))
      )
  )

noncomputable def _object_w7 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
let _wd_1_1 := (Litex.div (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(Litex.min _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((3 : ℂ) / (2 : ℂ)) ((3 : ℝ) / (2 : ℝ)) (by norm_num))))))

noncomputable def _object_w8 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)))

theorem h_22 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  let _equal_wd_1_1 := (_object_w8 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        let _equal_wd_1_1 := (_object_w8 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 ((Min.min (-2 : ℝ) ((3 : ℝ) / (2 : ℝ)) : ℝ) : ℂ) (- (2 : ℂ)) (let _extremum := _equal_wd_1_0;
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum (-2 : ℝ) ((3 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (((-2 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_1_0).val.right).wd.1 ((_equal_wd_1_0).val.right).wd.2.1 ((_equal_wd_1_0).val.right).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (2 : ℂ)) = ((((3 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
      )
  )

noncomputable def _object_w9 := (let _wd_1_0 := (_object_w6 (M := M));
let _wd_1_1 := (Litex.number (M := M) (0.5 : ℂ));
(Litex.max _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (_object_w6 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((_object_w6 (M := M))).wd.1 ((_object_w6 (M := M))).wd.2.1 ((_object_w6 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (0.5 : ℂ) (0.5 : ℝ) (by norm_num))))

theorem h_35 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0.5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0.5 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0.5 : ℂ)) ((Max.max ((1 : ℝ) / (3 : ℝ)) ((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ) (0.5 : ℂ) (let _extremum := _equal_wd_1_0;
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum ((1 : ℝ) / (3 : ℝ)) ((1 : ℝ) / (2 : ℝ)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) ((_object_w6 (M := M))).wd.1 ((_object_w6 (M := M))).wd.2.1 ((_object_w6 (M := M))).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((((1 : ℝ) / (3 : ℝ)) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (0.5 : ℂ))).trans (congrArg M.number (by norm_num : (0.5 : ℂ) = ((((1 : ℝ) / (2 : ℝ)) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0.5 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w11 := (let _wd_1_0 := (let _wd_2_0 := (_object_w8 (M := M));
let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.max _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := (_object_w8 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_object_w8 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (2 : ℂ)) (-2 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (3 : ℂ) (3 : ℝ) (by norm_num))));
let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
(Litex.min _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((Max.max (-2 : ℝ) (3 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := _atomic_wd_1_0;
  let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
  Litex.minMaxDenoteReal _extremum (-2 : ℝ) (3 : ℝ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_object_w8 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (((-2 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Max.max (-2 : ℝ) (3 : ℝ) : ℝ) : ℂ) (3 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))))

theorem h_39 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) ((Min.min (3 : ℝ) (4 : ℝ) : ℝ) : ℂ) (3 : ℂ) (let _extremum := _equal_wd_1_0;
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum (3 : ℝ) (4 : ℝ) (((let _extremum := (_equal_wd_1_0).val.left;
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum (-2 : ℝ) (3 : ℝ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_object_w8 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (((-2 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))))).trans (congrArg M.number (by norm_num : ((Max.max (-2 : ℝ) (3 : ℝ) : ℝ) : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (((4 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w12 := (Litex.max (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)))

theorem h_47 : (by
  let _equal_wd_1_0 := (_object_w12 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) ((Max.max (2 : ℝ) (2 : ℝ) : ℝ) : ℂ) (2 : ℂ) (let _extremum := _equal_wd_1_0;
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum (2 : ℝ) (2 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w14 := (let _wd_1_0 := (_object_w1 (M := M));
let _wd_1_1 := (_object_w3 (M := M));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (3 : ℂ) (Litex.C (M := M)) (((let _extremum := (_object_w1 (M := M));
  let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
  Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))))).trans (congrArg M.number (by norm_num : ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) = (3 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)))) (by
  let _atomic_wd_1_0 := (_object_w3 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (5 : ℂ) (Litex.C (M := M)) (((let _extremum := (_object_w3 (M := M));
  let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
  Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))))).trans (congrArg M.number (by norm_num : ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) = (5 : ℂ)))) (Litex.numberInC (M := M) (5 : ℂ))))))

theorem h_51 : (by
  let _equal_wd_1_0 := (_object_w14 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (8 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w14 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (8 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (8 : ℂ)) (((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) + ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ)) (8 : ℂ) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _extremum := (_object_w1 (M := M));
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (let _extremum := (_object_w3 (M := M));
        let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
        Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))))) (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)) (by norm_num))))
      )
  )

theorem h_55 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  let _atomic_wd_1_1 := (_object_w3 (M := M))
  exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          let _atomic_wd_1_1 := (_object_w3 (M := M))
          exact ((Litex.NativeBridge.lt_iff_asReal _atomic_wd_1_0 _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w1 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (3 : ℝ) (by norm_num)))) (by
            let _atomic_wd_2_0 := (_object_w3 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w3 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (5 : ℝ) (by norm_num))))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w1 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_0 (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w1 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (3 : ℝ) (by norm_num))))).symm.trans (((let _extremum := (_object_w1 (M := M));
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := (_object_w3 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w3 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (5 : ℝ) (by norm_num)))) = (5 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := (_object_w3 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w3 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Max.max (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (5 : ℝ) (by norm_num))))).symm.trans (((let _extremum := (_object_w3 (M := M));
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
      )
  )

theorem h_61 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) ((_object_w14 (M := M))).val.right :=
  (by
    litex_complete =>
      exact (
        (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) ((_object_w14 (M := M))).val.left ((_object_w14 (M := M))).val.right (by
          let _atomic_wd_1_1 := (_object_w1 (M := M))
          exact ((Litex.NativeBridge.le_iff_asReal (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w1 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (3 : ℝ) (by norm_num))))).mpr (by
            have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
            have _litex_right_value : Litex.NativeBridge.asReal _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w1 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (3 : ℝ) (by norm_num)))) = (3 : ℝ) := by
              apply Complex.ofReal_injective
              exact M.number_injective ((Litex.NativeBridge.asReal_spec _atomic_wd_1_1 (by
            let _atomic_wd_2_0 := (_object_w1 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (Litex.R (M := M)) (let _extremum := (_object_w1 (M := M));
            let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
            Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ))))) (Litex.NativeBridge.numberInROfEq ((Min.min (3 : ℝ) (5 : ℝ) : ℝ) : ℂ) (3 : ℝ) (by norm_num))))).symm.trans (((let _extremum := (_object_w1 (M := M));
          let _member : Litex.In _extremum Litex.C := Litex.realToComplex _extremum (Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2);
          Litex.minMaxDenoteReal _extremum (3 : ℝ) (5 : ℝ) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (((3 : ℝ) : ℝ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (((5 : ℝ) : ℝ) : ℂ)))))).trans (congrArg M.number (by norm_num))))
            exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r ≤ _litex_s) _litex_left_value _litex_right_value) (by norm_num)))) (h_55 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_min_x5f_max_x5f_evaluation_x2f_statement_x2e_lit
