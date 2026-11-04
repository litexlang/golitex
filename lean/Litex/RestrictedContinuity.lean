import Litex.GlobalContinuity

universe u
open Filter
open scoped Topology
namespace Litex

theorem functionContinuousOfRealOperationOn {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f) (raw : M.Value → M.Value) (operation : ℝ → ℝ)
    (numbers : ∀ x : ℝ, raw (M.number (x : ℂ)) = M.number (operation x : ℂ))
    (continuous : ∀ p : ℝ, M.mem (M.number (p : ℂ)) (F.domainValue f) → ContinuousAt operation p)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = raw x) :
    FunctionContinuousValue M f := by
  intro point hp
  have hfc := hf
  obtain ⟨signature,hfn,inputReal,_⟩ := hfc
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpoint⟩ := (M.real_members point).mp (inputReal point (hdomain ▸ hp))
  have hpnum : M.mem (M.number (p : ℂ)) (F.domainValue f) := hpoint ▸ hp
  have heq : ∀ x ∈ continuityApproachSet M .both f p, observeRealFunction f x = operation x := by
    intro x hx
    have equation := (formula (M.number (x : ℂ)) hx.1).trans (numbers x)
    unfold observeRealFunction
    rw [equation,observeRealValue_number]
  rw [hpoint]
  exact (functionContinuity_iff_native .both f hf p hpnum).mpr
    ((continuous p hpnum).continuousWithinAt.congr_of_mem heq ⟨hpnum,trivial⟩)

theorem functionContinuousOfLn {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (positive : ∀ x, M.mem x (F.domainValue f) → RealLtValue M (M.number 0) x)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = realUnaryValue Real.log x) :
    FunctionContinuousValue M f := by
  apply functionContinuousOfRealOperationOn f hf (realUnaryValue Real.log) Real.log
    (realUnaryValue_number Real.log) _ formula
  intro p hp
  exact Real.continuousAt_log (ne_of_gt ((realLtValue_numbers 0 p).mp (positive _ hp)))

theorem functionContinuousOfTan {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (nonzero : ∀ x, M.mem x (F.domainValue f) → realUnaryValue Real.cos x ≠ M.number 0)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = realUnaryValue Real.tan x) :
    FunctionContinuousValue M f := by
  apply functionContinuousOfRealOperationOn f hf (realUnaryValue Real.tan) Real.tan
    (realUnaryValue_number Real.tan) _ formula
  intro p hp
  have hcos : Real.cos p ≠ 0 := by
    intro h
    apply nonzero _ hp
    rw [realUnaryValue_number,h,Complex.ofReal_zero]
  have hfun : Real.tan = (fun x : ℝ => Real.sin x / Real.cos x) := by
    funext x
    exact Real.tan_eq_sin_div_cos x
  rw [hfun]
  exact Real.continuous_sin.continuousAt.div Real.continuous_cos.continuousAt hcos

theorem functionContinuousOfCot {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (nonzero : ∀ x, M.mem x (F.domainValue f) → realUnaryValue Real.sin x ≠ M.number 0)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = realUnaryValue nativeCot x) :
    FunctionContinuousValue M f := by
  apply functionContinuousOfRealOperationOn f hf (realUnaryValue nativeCot) nativeCot
    (realUnaryValue_number nativeCot) _ formula
  intro p hp
  apply Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt
  intro h
  apply nonzero _ hp
  rw [realUnaryValue_number,h,Complex.ofReal_zero]

theorem functionContinuousOfSec {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (nonzero : ∀ x, M.mem x (F.domainValue f) → realUnaryValue Real.cos x ≠ M.number 0)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = realUnaryValue nativeSec x) :
    FunctionContinuousValue M f := by
  apply functionContinuousOfRealOperationOn f hf (realUnaryValue nativeSec) nativeSec
    (realUnaryValue_number nativeSec) _ formula
  intro p hp
  apply continuousAt_const.div Real.continuous_cos.continuousAt
  intro h
  apply nonzero _ hp
  rw [realUnaryValue_number,h,Complex.ofReal_zero]

theorem functionContinuousOfCsc {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (nonzero : ∀ x, M.mem x (F.domainValue f) → realUnaryValue Real.sin x ≠ M.number 0)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = realUnaryValue nativeCsc x) :
    FunctionContinuousValue M f := by
  apply functionContinuousOfRealOperationOn f hf (realUnaryValue nativeCsc) nativeCsc
    (realUnaryValue_number nativeCsc) _ formula
  intro p hp
  apply continuousAt_const.div Real.continuous_sin.continuousAt
  intro h
  apply nonzero _ hp
  rw [realUnaryValue_number,h,Complex.ofReal_zero]

theorem functionContinuousOfCoth {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (nonzero : ∀ x, M.mem x (F.domainValue f) → x ≠ M.number 0)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = realUnaryValue nativeCoth x) :
    FunctionContinuousValue M f := by
  apply functionContinuousOfRealOperationOn f hf (realUnaryValue nativeCoth) nativeCoth
    (realUnaryValue_number nativeCoth) _ formula
  intro p hp
  apply Real.continuous_cosh.continuousAt.div Real.continuous_sinh.continuousAt
  apply Real.sinh_ne_zero.mpr
  intro h
  apply nonzero _ hp
  rw [h,Complex.ofReal_zero]

theorem functionContinuousOfCsch {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (nonzero : ∀ x, M.mem x (F.domainValue f) → x ≠ M.number 0)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = realUnaryValue nativeCsch x) :
    FunctionContinuousValue M f := by
  apply functionContinuousOfRealOperationOn f hf (realUnaryValue nativeCsch) nativeCsch
    (realUnaryValue_number nativeCsch) _ formula
  intro p hp
  apply continuousAt_const.div Real.continuous_sinh.continuousAt
  apply Real.sinh_ne_zero.mpr
  intro h
  apply nonzero _ hp
  rw [h,Complex.ofReal_zero]

theorem functionContinuousOfSqrt {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x = sqrtValue x) :
    FunctionContinuousValue M f := by
  exact functionContinuousOfRealOperationOn f hf sqrtValue Real.sqrt sqrtValue_number
    (fun _ _ => Real.continuous_sqrt.continuousAt) formula

theorem functionContinuousOfLog {M : Semantics.{u}} [F : FunctionSemantics M]
    (f base : M.Value) (hf : RealFunctionValue M f)
    (hb : M.mem base (denote (RPos (M := M)))) (hone : base ≠ M.number 1)
    (positive : ∀ x, M.mem x (F.domainValue f) → RealLtValue M (M.number 0) x)
    (formula : ∀ x, M.mem x (F.domainValue f) → F.callValue f x =
      M.divValue (realUnaryValue Real.log x) (realUnaryValue Real.log base)) :
    FunctionContinuousValue M f := by
  let b := semanticObject base (M.member_isSet hb)
  have hbr := inRPos_real b hb
  let r := NativeBridge.asReal b hbr
  have hbase : base = M.number (r : ℂ) := NativeBridge.asReal_spec b hbr
  have hpbase : RealLtValue M (M.number 0) base := inRPos_positive b hb
  rw [hbase] at hpbase
  have hpos : 0 < r := (realLtValue_numbers 0 r).mp hpbase
  have hrone : r ≠ 1 := by
    intro h
    apply hone
    simpa only [h,Complex.ofReal_one] using hbase
  have hlog : ((Real.log r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one hpos hrone
  apply functionContinuousOfRealOperationOn f hf
    (fun x => M.divValue (realUnaryValue Real.log x) (realUnaryValue Real.log base))
    (fun x => Real.log x / Real.log r) _ _ formula
  · intro x
    rw [hbase,realUnaryValue_number,realUnaryValue_number,M.div_numbers _ _ hlog,
      ← Complex.ofReal_div]
  · intro p hp
    exact (Real.continuousAt_log (ne_of_gt ((realLtValue_numbers 0 p).mp (positive _ hp)))).div_const _

end Litex
