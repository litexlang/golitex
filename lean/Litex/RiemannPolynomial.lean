import Litex.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

universe u
namespace Litex
open Set MeasureTheory
open scoped BigOperators

/-- A finite partition with bounds valid on each closed cell. -/
structure ClosedDarbouxPartition (f : ℝ → ℝ) (a b : ℝ) where
  n : ℕ
  positive : 0 < n
  points : ℕ → ℝ
  lower : ℕ → ℝ
  upper : ℕ → ℝ
  first : points 0 = a
  last : points n = b
  increasing : ∀ i < n, points i < points (i+1)
  bounds : ∀ i < n, ∀ x ∈ Icc (points i) (points (i+1)), lower i ≤ f x ∧ f x ≤ upper i

def ClosedDarbouxPartition.lowerSum {f a b} (p : ClosedDarbouxPartition f a b) : ℝ :=
  ∑ i ∈ Finset.range p.n, p.lower i * (p.points (i+1)-p.points i)

def ClosedDarbouxPartition.upperSum {f a b} (p : ClosedDarbouxPartition f a b) : ℝ :=
  ∑ i ∈ Finset.range p.n, p.upper i * (p.points (i+1)-p.points i)

theorem continuousIntegralEnclosure (f : ℝ → ℝ) (hf : Continuous f)
    (a b ε : ℝ) (hab : a < b) (hε : 0 < ε) :
    ∃ p : ClosedDarbouxPartition f a b,
      p.lowerSum ≤ (∫ x in a..b, f x) ∧
      (∫ x in a..b, f x) ≤ p.upperSum ∧ p.upperSum-p.lowerSum < ε := by
  let η := ε / (4 * (b-a))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, close⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc a b)).uniformContinuousOn_of_continuous hf.continuousOn) η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((b-a)/δ)
  have hn0 : 0 < n := by
    have : 0 < (n : ℝ) := lt_trans (div_pos (sub_pos.mpr hab) hδ) hn
    exact_mod_cast this
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  let width := (b-a)/(n : ℝ)
  have hw : 0 < width := div_pos (sub_pos.mpr hab) hnR
  have hwδ : width < δ := by
    apply (div_lt_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hδ).mp hn
    nlinarith
  let point := fun i : ℕ => a + (i : ℝ)*width
  have first : point 0 = a := by simp [point]
  have last : point n = b := by dsimp [point, width]; field_simp; ring
  have step (i : ℕ) : point (i+1)-point i=width := by dsimp [point]; push_cast; ring
  have increasing (i : ℕ) : point i < point (i+1) := by linarith [step i]
  have inInterval (i : ℕ) (hi : i ≤ n) : point i ∈ Icc a b := by
    constructor
    · dsimp [point]; have h : 0 ≤ (i : ℝ)*width := mul_nonneg (Nat.cast_nonneg i) hw.le; linarith
    · have : (i : ℝ) ≤ n := by exact_mod_cast hi
      have h := mul_le_mul_of_nonneg_right this hw.le
      rw [← last]
      dsimp [point]
      linarith
  let lower := fun i => f (point i)-η
  let upper := fun i => f (point i)+η
  have bounds (i : ℕ) (hi : i < n) (x : ℝ) (hx : x ∈ Icc (point i) (point (i+1))) :
      lower i ≤ f x ∧ f x ≤ upper i := by
    have hpi := inInterval i (by omega)
    have hnext := inInterval (i+1) (by omega)
    have hxI : x ∈ Icc a b := ⟨le_trans hpi.1 hx.1, le_trans hx.2 hnext.2⟩
    have hd : dist x (point i) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith [step i, hx.2]
    have hclose := close x hxI (point i) hpi hd
    rw [Real.dist_eq] at hclose
    have hclose := abs_lt.mp hclose
    dsimp [lower, upper]
    constructor <;> linarith
  let p : ClosedDarbouxPartition f a b :=
    ⟨n, hn0, point, lower, upper, first, last, fun i _ => increasing i, bounds⟩
  have integrable (i : ℕ) : IntervalIntegrable f volume (point i) (point (i+1)) :=
    hf.intervalIntegrable _ _
  have sumIntegral := intervalIntegral.sum_integral_adjacent_intervals
    (fun i (_hi : i < n) => integrable i)
  rw [first, last] at sumIntegral
  have low : p.lowerSum ≤ ∫ x in a..b, f x := by
    rw [← sumIntegral]
    apply Finset.sum_le_sum
    intro i hi
    have hi := Finset.mem_range.mp hi
    have h := intervalIntegral.integral_mono_on (increasing i).le
      (intervalIntegrable_const (c := lower i)) (integrable i)
      (fun x hx => (bounds i hi x hx).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have high : (∫ x in a..b, f x) ≤ p.upperSum := by
    rw [← sumIntegral]
    apply Finset.sum_le_sum
    intro i hi
    have hi := Finset.mem_range.mp hi
    have h := intervalIntegral.integral_mono_on (increasing i).le
      (integrable i) (intervalIntegrable_const (c := upper i))
      (fun x hx => (bounds i hi x hx).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  refine ⟨p, low, high, ?_⟩
  change (∑ i ∈ Finset.range n, upper i*(point (i+1)-point i)) -
    (∑ i ∈ Finset.range n, lower i*(point (i+1)-point i)) < ε
  rw [← Finset.sum_sub_distrib]
  have term (i : ℕ) : upper i*(point (i+1)-point i)-lower i*(point (i+1)-point i)=2*η*width := by
    rw [step]; dsimp [upper, lower]; ring
  simp_rw [term]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have area : (n : ℝ)*width=b-a := by dsimp [width]; field_simp
  calc
    (n : ℝ)*(2*η*width) = 2*η*(b-a) := by rw [← area]; ring
    _ = ε/2 := by dsimp [η]; field_simp [ne_of_gt (sub_pos.mpr hab)]; ring
    _ < ε := by linarith
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]
open Set MeasureTheory
open scoped BigOperators

noncomputable def riemannNatGraph (lo hi : ℕ) (value : ℕ → ℝ) : M.Value :=
  F.graphValue (riemannIndexDomain (M.number (lo : ℂ)) (M.number (hi : ℂ)))
    (M.standard .real) (fun k => M.number (value (NativeBridge.integerValue k).toNat : ℂ))

theorem riemannNatGraph_mem (lo hi : ℕ) (value : ℕ → ℝ) :
    M.mem (riemannNatGraph (M := M) lo hi value)
      (riemannIndexFnValue (M.number (lo : ℂ)) (M.number (hi : ℂ))) :=
  F.graph_inFnSet _ _ _ (fun _ _ => NativeBridge.numberInR _)

theorem riemannNatGraph_call (lo hi k : ℕ) (value : ℕ → ℝ) (hlo : lo ≤ k) (hhi : k ≤ hi) :
    F.callValue (riemannNatGraph (M := M) lo hi value) (M.number (k : ℂ)) = M.number (value k : ℂ) := by
  have mem : M.mem (M.number (k : ℂ))
      (riemannIndexDomain (M.number (lo : ℂ)) (M.number (hi : ℂ))) := by
    simpa only [Int.cast_natCast] using riemannIndexDomain_number (M := M)
      (lo : ℤ) (hi : ℤ) (k : ℤ) (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  have body (j : M.Value) (_ : M.mem j (riemannIndexDomain (M.number (lo : ℂ)) (M.number (hi : ℂ)))) :
      M.mem (M.number (value (NativeBridge.integerValue j).toNat : ℂ)) (M.standard .real) :=
    (M.real_members _).mpr ⟨_, rfl⟩
  rw [riemannNatGraph, F.call_graphValue _ _ _ body _ mem]
  simp only [show (k : ℂ) = ((k : ℤ) : ℂ) by simp, NativeBridge.integerValue_number, Int.toNat_natCast]

theorem ClosedDarbouxPartition.ordered {f a b} (p : ClosedDarbouxPartition f a b)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.n) : p.points i ≤ p.points j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact le_trans (ih (by omega)) (p.increasing j (by omega)).le

theorem riemannCellIndex (n : ℕ) (k : M.Value)
    (hk : M.mem k (closedRangeValue (M.number 1) (M.number (n : ℂ)))) :
    ∃ i < n, k = M.number ((i+1 : ℕ) : ℂ) := by
  have hk' : M.mem k (closedRangeValue (M.number ((1 : ℤ) : ℂ)) (M.number ((n : ℤ) : ℂ))) := by
    simpa only [Int.cast_one, Int.cast_natCast] using hk
  obtain ⟨j, rfl, hj, hjn⟩ := (closedRangeValue_members (M := M) 1 (n : ℤ) _).mp hk'
  refine ⟨j.toNat-1, by omega, ?_⟩
  have eq : ((j.toNat-1+1 : ℕ) : ℤ) = j := by omega
  exact congrArg M.number (by exact_mod_cast eq.symm)

theorem closedPartitionEnclosure {g : ℝ → ℝ} {a b : ℝ}
    (p : ClosedDarbouxPartition g a b) (hab : a < b) (f : M.Value)
    (formula : ∀ x ∈ Icc a b, F.callValue f (M.number (x : ℂ)) = M.number (g x : ℂ)) :
    DarbouxEnclosureValue f (M.number (a : ℂ)) (M.number (b : ℂ)) (M.number (p.n : ℂ))
      (riemannNatGraph 0 p.n p.points)
      (riemannNatGraph 1 p.n (fun k => p.lower (k-1)))
      (riemannNatGraph 1 p.n (fun k => p.upper (k-1))) := by
  refine ⟨(realLtValue_numbers _ _).mpr hab, ?_, by simpa only [Nat.cast_zero] using riemannNatGraph_mem (M := M) 0 p.n p.points,
    by simpa only [Nat.cast_one] using riemannNatGraph_mem (M := M) 1 p.n (fun k => p.lower (k-1)),
    by simpa only [Nat.cast_one] using riemannNatGraph_mem (M := M) 1 p.n (fun k => p.upper (k-1)), ?_, ?_, ?_, ?_⟩
  · exact numberInNPosOfEq (p.n : ℂ) p.n rfl p.positive
  · simpa only [Nat.cast_zero, p.first] using riemannNatGraph_call (M := M) 0 p.n 0 p.points (by omega) (by omega)
  · rw [riemannNatGraph_call 0 p.n p.n _ (by omega) (by omega), p.last]
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := riemannCellIndex p.n k hk
    simp only [M.sub_numbers, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    have rightCall := riemannNatGraph_call (M := M) 0 p.n (i+1) p.points (by omega) (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at rightCall
    rw [riemannNatGraph_call 0 p.n i _ (by omega) (by omega), rightCall]
    refine ⟨(realLtValue_numbers _ _).mpr (p.increasing i hi),
      (realLeValue_numbers _ _).mpr ?_, (realLeValue_numbers _ _).mpr ?_⟩
    · simpa only [p.first] using p.ordered 0 i (by omega) (by omega)
    · simpa only [p.last] using p.ordered (i+1) p.n (by omega) le_rfl
  · intro k hk x hx left right
    obtain ⟨i, hi, rfl⟩ := riemannCellIndex p.n k hk
    obtain ⟨hxR, hax, hxb⟩ := (F.sep_members _ _ _).mp hx
    obtain ⟨xr, rfl⟩ := (M.real_members x).mp hxR
    simp only [M.sub_numbers, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at left
    rw [riemannNatGraph_call 0 p.n i _ (by omega) (by omega)] at left
    rw [riemannNatGraph_call 0 p.n (i+1) _ (by omega) (by omega)] at right
    have hxI : xr ∈ Icc a b := ⟨(realLeValue_numbers _ _).mp hax, (realLeValue_numbers _ _).mp hxb⟩
    rw [formula xr hxI,
      riemannNatGraph_call 1 p.n (i+1) _ (by omega) (by omega),
      riemannNatGraph_call 1 p.n (i+1) _ (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    have bounds := p.bounds i hi xr ⟨(realLeValue_numbers _ _).mp left, (realLeValue_numbers _ _).mp right⟩
    exact ⟨(realLeValue_numbers _ _).mpr bounds.1, (realLeValue_numbers _ _).mpr bounds.2⟩

theorem closedPartitionSum {g : ℝ → ℝ} {a b : ℝ}
    (p : ClosedDarbouxPartition g a b) (height : ℕ → ℝ) :
    riemannStepSumValue (M := M) (M.number (p.n : ℂ))
      (riemannNatGraph 0 p.n p.points) (riemannNatGraph 1 p.n (fun k => height (k-1))) =
      M.number ((∑ i ∈ Finset.range p.n, height i*(p.points (i+1)-p.points i) : ℝ) : ℂ) := by
  have hp := riemannNatGraph_mem (M := M) 0 p.n p.points
  have hh := riemannNatGraph_mem (M := M) 1 p.n (fun k => height (k-1))
  rw [riemannStepSumValue_nat (by simpa only [Int.cast_zero,Int.cast_natCast,Nat.cast_zero] using hp)
    (by simpa only [Int.cast_one,Int.cast_natCast,Nat.cast_one] using hh)]
  apply congrArg M.number
  apply congrArg Complex.ofReal
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_range.mp hi
  rw [riemannNatGraph_call 1 p.n (i+1) _ (by omega) (by omega),
    riemannNatGraph_call 0 p.n (i+1) _ (by omega) (by omega),
    riemannNatGraph_call 0 p.n i _ (by omega) (by omega)]
  simp only [Nat.add_sub_cancel, observeRealValue_number]

theorem darbouxApproximationOfContinuous (f : M.Value) (g : ℝ → ℝ)
    (hg : Continuous g) (a b : ℝ)
    (formula : ∀ x ∈ Icc a b, F.callValue f (M.number (x : ℂ)) = M.number (g x : ℂ)) :
    DarbouxApproximationValue f (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number ((∫ x in a..b, g x : ℝ) : ℂ)) := by
  intro ε hε order
  obtain ⟨er, εeq, her⟩ := ((positiveReal_members ε).mp hε).2
  have hab := (realLtValue_numbers a b).mp order
  obtain ⟨p, low, high, gap⟩ := continuousIntegralEnclosure g hg a b er hab her
  let N := semanticObject (M := M) (M.number (p.n : ℂ)) (M.member_isSet (NativeBridge.numberInR _))
  let P := semanticObject (M := M) (riemannNatGraph 0 p.n p.points) (M.member_isSet (riemannNatGraph_mem 0 p.n p.points))
  let L := semanticObject (M := M) (riemannNatGraph 1 p.n (fun k => p.lower (k-1))) (M.member_isSet (riemannNatGraph_mem 1 p.n (fun k => p.lower (k-1))))
  let U := semanticObject (M := M) (riemannNatGraph 1 p.n (fun k => p.upper (k-1))) (M.member_isSet (riemannNatGraph_mem 1 p.n (fun k => p.upper (k-1))))
  let LS := semanticObject (M := M) (M.number (p.lowerSum : ℂ)) (M.member_isSet (NativeBridge.numberInR _))
  let US := semanticObject (M := M) (M.number (p.upperSum : ℂ)) (M.member_isSet (NativeBridge.numberInR _))
  refine ⟨N, ?_, P, ?_, L, ?_, U, ?_, LS, ?_, US, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact numberInNPosOfEq _ p.n rfl p.positive
  · simpa only [N, P, L, U, semanticObject_denote, Nat.cast_zero, Nat.cast_one] using riemannNatGraph_mem (M := M) 0 p.n p.points
  · simpa only [N, P, L, U, semanticObject_denote, Nat.cast_zero, Nat.cast_one] using riemannNatGraph_mem (M := M) 1 p.n (fun k => p.lower (k-1))
  · simpa only [N, P, L, U, semanticObject_denote, Nat.cast_zero, Nat.cast_one] using riemannNatGraph_mem (M := M) 1 p.n (fun k => p.upper (k-1))
  · exact NativeBridge.numberInR _
  · exact NativeBridge.numberInR _
  · exact closedPartitionEnclosure p hab f formula
  · exact (closedPartitionSum p p.lower).symm
  · exact (closedPartitionSum p p.upper).symm
  · exact (realLeValue_numbers _ _).mpr low
  · exact (realLeValue_numbers _ _).mpr high
  · dsimp only [US, LS, semanticObject_denote]
    rw [M.sub_numbers, ← Complex.ofReal_sub, εeq]
    exact (realLtValue_numbers _ _).mpr gap
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]
open Set MeasureTheory
open scoped BigOperators

/-- The semantic expression and the exact integral are certified together. -/
def PolynomialIntegralFormula (raw : ℝ → M.Value) (a b : ℝ) (value : M.Value) : Prop :=
  ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, raw x = M.number (g x : ℂ)) ∧
    value = M.number ((∫ x in a..b, g x : ℝ) : ℂ)

omit F in
theorem polynomialIntegralConstant (c : M.Value) (hc : M.mem c (M.standard .real)) (a b : ℝ) :
    PolynomialIntegralFormula (fun _ => c) a b
      (M.mulValue c (M.subValue (M.number (b : ℂ)) (M.number (a : ℂ)))) := by
  obtain ⟨r, rfl⟩ := (M.real_members c).mp hc
  refine ⟨fun _ => r, continuous_const, fun _ => rfl, ?_⟩
  rw [M.sub_numbers, M.mul_numbers, intervalIntegral.integral_const]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub]
  congr 1
  ring

omit F in
theorem polynomialIntegralVariable (a b : ℝ) :
    PolynomialIntegralFormula (fun x => M.number (x : ℂ)) a b
      (M.divValue (M.subValue (M.powValue (M.number (b : ℂ)) (M.addValue (M.number 1) (M.number 1)))
        (M.powValue (M.number (a : ℂ)) (M.addValue (M.number 1) (M.number 1)))) (M.addValue (M.number 1) (M.number 1))) := by
  refine ⟨id, continuous_id, fun _ => rfl, ?_⟩
  rw [show M.addValue (M.number 1) (M.number 1) = M.number ((2 : ℕ) : ℂ) by rw [M.add_numbers]; norm_num,
    M.pow_numbers_nat, M.pow_numbers_nat, M.sub_numbers, M.div_numbers _ _ (by norm_num)]
  simpa only [id_eq, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ofNat, Nat.cast_ofNat]
    using congrArg (fun r : ℝ => M.number (r : ℂ)) (integral_id (a := a) (b := b)).symm

omit F in
theorem polynomialIntegralPower (a b : ℝ) (n : ℕ) :
    PolynomialIntegralFormula (fun x => M.powValue (M.number (x : ℂ)) (M.number (n : ℂ))) a b
      (M.divValue
        (M.subValue (M.powValue (M.number (b : ℂ)) (M.addValue (M.number (n : ℂ)) (M.number 1)))
          (M.powValue (M.number (a : ℂ)) (M.addValue (M.number (n : ℂ)) (M.number 1))))
        (M.addValue (M.number (n : ℂ)) (M.number 1))) := by
  refine ⟨fun x => x^n, continuous_id.pow n, ?_, ?_⟩
  · intro x
    dsimp only
    rw [M.pow_numbers_nat, Complex.ofReal_pow]
  · rw [M.add_numbers, show (n : ℂ)+1=((n+1 : ℕ) : ℂ) by push_cast; rfl,
      M.pow_numbers_nat, M.pow_numbers_nat, M.sub_numbers, M.div_numbers _ _ (by exact_mod_cast Nat.succ_ne_zero n)]
    simpa only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_one, Nat.cast_add, Nat.cast_one]
      using congrArg (fun r : ℝ => M.number (r : ℂ)) (integral_pow (n := n) (a := a) (b := b)).symm

omit F in
theorem polynomialIntegralAdd (f g : ℝ → M.Value) (a b : ℝ) (v w : M.Value)
    (hf : PolynomialIntegralFormula f a b v) (hg : PolynomialIntegralFormula g a b w) :
    PolynomialIntegralFormula (fun x => M.addValue (f x) (g x)) a b (M.addValue v w) := by
  obtain ⟨p, hp, ep, ev⟩ := hf
  obtain ⟨q, hq, eq, ew⟩ := hg
  refine ⟨fun x => p x+q x, hp.add hq, ?_, ?_⟩
  · intro x
    dsimp only
    rw [ep, eq, M.add_numbers, Complex.ofReal_add]
  · rw [ev, ew, M.add_numbers, intervalIntegral.integral_add (hp.intervalIntegrable _ _) (hq.intervalIntegrable _ _), Complex.ofReal_add]

omit F in
theorem polynomialIntegralSub (f g : ℝ → M.Value) (a b : ℝ) (v w : M.Value)
    (hf : PolynomialIntegralFormula f a b v) (hg : PolynomialIntegralFormula g a b w) :
    PolynomialIntegralFormula (fun x => M.subValue (f x) (g x)) a b (M.subValue v w) := by
  obtain ⟨p, hp, ep, ev⟩ := hf
  obtain ⟨q, hq, eq, ew⟩ := hg
  refine ⟨fun x => p x-q x, hp.sub hq, ?_, ?_⟩
  · intro x
    dsimp only
    rw [ep, eq, M.sub_numbers, Complex.ofReal_sub]
  · rw [ev, ew, M.sub_numbers, intervalIntegral.integral_sub (hp.intervalIntegrable _ _) (hq.intervalIntegrable _ _), Complex.ofReal_sub]

omit F in
theorem polynomialIntegralScale (f : ℝ → M.Value) (a b : ℝ) (v c : M.Value)
    (hc : M.mem c (M.standard .real)) (hf : PolynomialIntegralFormula f a b v) :
    PolynomialIntegralFormula (fun x => M.mulValue c (f x)) a b (M.mulValue c v) := by
  obtain ⟨r, rfl⟩ := (M.real_members c).mp hc
  obtain ⟨p, hp, ep, ev⟩ := hf
  refine ⟨fun x => r*p x, continuous_const.mul hp, ?_, ?_⟩
  · intro x
    dsimp only
    rw [ep, M.mul_numbers, Complex.ofReal_mul]
  · rw [ev, M.mul_numbers, intervalIntegral.integral_const_mul, Complex.ofReal_mul]

omit F in
theorem polynomialIntegralDivide (f : ℝ → M.Value) (a b : ℝ) (v c : M.Value)
    (hc : M.mem c (M.standard .real)) (hc0 : c ≠ M.number 0)
    (hf : PolynomialIntegralFormula f a b v) :
    PolynomialIntegralFormula (fun x => M.divValue (f x) c) a b (M.divValue v c) := by
  obtain ⟨r, rfl⟩ := (M.real_members c).mp hc
  have hr : (r : ℂ) ≠ 0 := fun h => hc0 (by rw [h])
  obtain ⟨p, hp, ep, ev⟩ := hf
  refine ⟨fun x => p x/r, hp.div_const r, ?_, ?_⟩
  · intro x
    dsimp only
    rw [ep, M.div_numbers _ _ hr, Complex.ofReal_div]
  · rw [ev, M.div_numbers _ _ hr, intervalIntegral.integral_div, Complex.ofReal_div]
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]
open Set MeasureTheory

theorem riemannIntegralOfContinuousFormula (f a b : M.Value)
    (hf : RealFunctionValue M f)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (cover : ∀ x, M.mem x (riemannIntervalValue a b) → M.mem x (F.domainValue f))
    (g : ℝ → ℝ) (hg : Continuous g)
    (formula : ∀ x : ℝ, M.mem (M.number (x : ℂ)) (riemannIntervalValue a b) →
      F.callValue f (M.number (x : ℂ)) = M.number (g x : ℂ)) :
    HasRiemannIntegralValue M f a b
      (M.number ((∫ x in observeRealValue a..observeRealValue b, g x : ℝ) : ℂ)) := by
  obtain ⟨ar, rfl⟩ := (M.real_members a).mp ha
  obtain ⟨br, rfl⟩ := (M.real_members b).mp hb
  simp only [observeRealValue_number]
  have interval (x : ℝ) :
      M.mem (M.number (x : ℂ)) (riemannIntervalValue (M.number (ar : ℂ)) (M.number (br : ℂ))) ↔
      x ∈ Icc (Min.min ar br) (Max.max ar br) := by
    unfold riemannIntervalValue
    rw [minMaxValue_number, minMaxValue_number]
    simp only [Bool.false_eq_true, ite_false, ite_true, riemannClosedIntervalValue,
      F.sep_members, realBound]
    exact ⟨fun h => ⟨(realLeValue_numbers _ _).mp h.2.1,(realLeValue_numbers _ _).mp h.2.2⟩, fun h => ⟨NativeBridge.numberInR _,(realLeValue_numbers _ _).mpr h.1,(realLeValue_numbers _ _).mpr h.2⟩⟩
  have callReal (x : M.Value)
      (hx : M.mem x (riemannIntervalValue (M.number (ar : ℂ)) (M.number (br : ℂ)))) :
      M.mem (F.callValue f x) (M.standard .real) := by
    obtain ⟨signature, member, _, output⟩ := hf
    exact output _ (F.call_mem _ _ _ _ member ((F.domainValue_eq signature.domain_isSet member) ▸ cover x hx))
  let D := F.sepValue (riemannIntervalValue (M.number (ar : ℂ)) (M.number (br : ℂ))) (fun _ => True)
  let graph := F.graphValue D (M.standard .real) (F.callValue f)
  have graphMember : M.mem graph (F.fnSetValue D (M.standard .real)) :=
    F.graph_inFnSet _ _ _ (fun x hx => callReal x ((F.sep_members _ _ _).mp hx).1)
  have rangePoint (y : M.Value)
      (hy : M.mem y (riemannRestrictedRangeValue f (M.number (ar : ℂ)) (M.number (br : ℂ)))) :
      ∃ x ∈ Icc (Min.min ar br) (Max.max ar br), y=M.number (g x : ℂ) := by
    change M.mem y (F.rangeValue graph) at hy
    obtain ⟨x,hxy⟩ := ((F.range_spec (isSet (R (M := M))) graphMember).2 y).mp hy
    obtain ⟨hx,_,hvalue⟩ := (F.pair_mem_graph D (M.standard .real) (F.callValue f) x y).mp hxy
    have hx := ((F.sep_members _ _ _).mp hx).1
    have hxR : M.mem x (M.standard .real) := by
      unfold riemannIntervalValue riemannClosedIntervalValue at hx
      exact ((F.sep_members _ _ _).mp hx).1
    obtain ⟨xr,rfl⟩ := (M.real_members x).mp hxR
    exact ⟨xr,(interval xr).mp hx,hvalue.trans (formula xr hx)⟩
  obtain ⟨lo,hlo⟩ := isCompact_Icc.bddBelow_image hg.continuousOn
  obtain ⟨hi,hhi⟩ := isCompact_Icc.bddAbove_image hg.continuousOn
  let low := semanticObject (M := M) (M.number (lo : ℂ)) (M.member_isSet (NativeBridge.numberInR lo))
  let high := semanticObject (M := M) (M.number (hi : ℂ)) (M.member_isSet (NativeBridge.numberInR hi))
  refine ⟨NativeBridge.numberInR _,ha,hb,cover,⟨?_,?_⟩,?_,?_⟩
  · refine ⟨low, NativeBridge.numberInR lo, ?_⟩
    intro y hy
    obtain ⟨x,hx,rfl⟩ := rangePoint y hy
    exact (realLeValue_numbers _ _).mpr (hlo (mem_image_of_mem g hx))
  · refine ⟨high, NativeBridge.numberInR hi, ?_⟩
    intro y hy
    obtain ⟨x,hx,rfl⟩ := rangePoint y hy
    exact (realLeValue_numbers _ _).mpr (hhi (mem_image_of_mem g hx))
  · by_cases h : M.number (ar : ℂ)=M.number (br : ℂ)
    · right
      have he := Complex.ofReal_injective (M.number_injective h)
      simp only [he, intervalIntegral.integral_same, Complex.ofReal_zero]
    · exact Or.inl h
  · rw [minMaxValue_number, minMaxValue_number, riemannOrientedValue_number]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    have orient : Real.sign (br-ar)*(∫ x in ar..br, g x) = ∫ x in Min.min ar br..Max.max ar br, g x := by
      rcases lt_trichotomy ar br with h | h | h
      · simp only [min_eq_left h.le,max_eq_right h.le,Real.sign_of_pos (sub_pos.mpr h),one_mul]
      · simp only [h, sub_self,Real.sign_zero,zero_mul, min_self,max_self,intervalIntegral.integral_same]
      · rw [min_eq_right h.le,max_eq_left h.le,Real.sign_of_neg (sub_neg.mpr h),neg_one_mul,intervalIntegral.integral_symm]
        simp only [neg_neg]
    rw [orient]
    exact darbouxApproximationOfContinuous f g hg _ _ (fun x hx => formula x ((interval x).mpr hx))

theorem riemannIntegralOfPolynomialFormula (f a b value : M.Value)
    (hf : RealFunctionValue M f)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (cover : ∀ x, M.mem x (riemannIntervalValue a b) → M.mem x (F.domainValue f))
    (raw : ℝ → M.Value)
    (formula : ∀ x : ℝ, M.mem (M.number (x : ℂ)) (riemannIntervalValue a b) → F.callValue f (M.number (x : ℂ))=raw x)
    (proof : PolynomialIntegralFormula raw (observeRealValue a) (observeRealValue b) value) :
    HasRiemannIntegralValue M f a b value := by
  obtain ⟨g,hg,eq,hvalue⟩ := proof
  rw [hvalue]
  exact riemannIntegralOfContinuousFormula f a b hf ha hb cover g hg
    (fun x hx => (formula x hx).trans (eq x))
end Litex

namespace Litex
variable {M : Semantics.{u}}
open MeasureTheory

theorem polynomialIntegralNeg (f : ℝ → M.Value) (a b : ℝ) (v : M.Value)
    (hf : PolynomialIntegralFormula f a b v) :
    PolynomialIntegralFormula (fun x => M.negValue (f x)) a b (M.subValue (M.number 0) v) := by
  obtain ⟨p,hp,ep,ev⟩ := hf
  refine ⟨fun x => -p x,hp.neg,?_,?_⟩
  · intro x
    dsimp only
    rw [ep,M.neg_numbers,Complex.ofReal_neg]
  · rw [ev,M.sub_numbers,intervalIntegral.integral_neg]
    simp only [zero_sub,Complex.ofReal_neg]

theorem polynomialIntegralScaleRight (f : ℝ → M.Value) (a b : ℝ) (v c : M.Value)
    (hc : M.mem c (M.standard .real)) (hf : PolynomialIntegralFormula f a b v) :
    PolynomialIntegralFormula (fun x => M.mulValue (f x) c) a b (M.mulValue c v) := by
  obtain ⟨r,rfl⟩ := (M.real_members c).mp hc
  obtain ⟨p,hp,ep,ev⟩ := hf
  refine ⟨fun x => p x*r,hp.mul continuous_const,?_,?_⟩
  · intro x
    dsimp only
    rw [ep,M.mul_numbers,Complex.ofReal_mul]
  · rw [ev,M.mul_numbers,intervalIntegral.integral_mul_const,Complex.ofReal_mul]
    congr 1
    ring
end Litex
