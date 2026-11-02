import Litex.Limits
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Set.Union

universe u v w x r

namespace Litex

open Filter
open scoped Topology

/-- A fixed real observation of a semantic value; zero outside the real image. -/
noncomputable def observeRealValue {M : Semantics.{u}} (value : M.Value) : ℝ := by
  classical
  exact if h : ∃ r : ℝ, value = M.number (r : ℂ) then Classical.choose h else 0

theorem observeRealValue_number {M : Semantics.{u}} (r : ℝ) :
    observeRealValue (M.number (r : ℂ)) = r := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hs : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold observeRealValue
  rw [dif_pos h, hs]

noncomputable def observeRealFunction {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (x : ℝ) : ℝ := observeRealValue (F.callValue f (M.number (x : ℂ)))

theorem observeRealFunction_spec {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f) (x : ℝ)
    (hx : M.mem (M.number (x : ℂ)) (F.domainValue f)) :
    F.callValue f (M.number (x : ℂ)) = M.number (observeRealFunction f x : ℂ) := by
  obtain ⟨signature, hfn, _, houtput⟩ := hf
  have hd := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨y, hy⟩ := (M.real_members _).mp
    (houtput _ (F.call_mem _ _ _ _ hfn (hd ▸ hx)))
  change F.callValue f (M.number (x : ℂ)) = M.number (observeRealValue (F.callValue f (M.number (x : ℂ))) : ℂ)
  rw [hy, observeRealValue_number]

def finiteApproachSet (M : Semantics.{u}) [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (point : ℝ) : Set ℝ :=
  {x | M.mem (M.number (x : ℂ)) (F.domainValue f) ∧ 0 < finiteLimitDistance side point x}

theorem finiteFunctionEpsilon_iff_tendsto {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (hf : RealFunctionValue M f) (point value : ℝ) :
    FiniteFunctionEpsilonValue M side f point value ↔
      Tendsto (observeRealFunction f) (nhdsWithin point (finiteApproachSet M side f point)) (𝓝 value) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro he epsilon hepsilon
    obtain ⟨delta, hdelta, hcontrol⟩ := he epsilon hepsilon
    refine ⟨delta, hdelta, ?_⟩
    intro x hx hnear
    have hdist := finiteLimitDistance_eq_abs side point x hx.2
    have hclose : finiteLimitDistance side point x < delta := by
      simpa only [hdist, Real.dist_eq] using hnear
    obtain ⟨y, hy, hestimate⟩ := hcontrol x hx.1 hx.2 hclose
    have observed : observeRealFunction f x = y := by
      unfold observeRealFunction
      rw [hy, observeRealValue_number]
    simpa only [observed, Real.dist_eq] using hestimate
  · intro he epsilon hepsilon
    obtain ⟨delta, hdelta, hcontrol⟩ := he epsilon hepsilon
    refine ⟨delta, hdelta, ?_⟩
    intro x hx hpositive hnear
    have hdist := finiteLimitDistance_eq_abs side point x hpositive
    refine ⟨observeRealFunction f x, observeRealFunction_spec f hf x hx, ?_⟩
    have estimate := hcontrol (x := x) ⟨hx, hpositive⟩
      (by simpa only [Real.dist_eq, ← hdist] using hnear)
    simpa only [Real.dist_eq] using estimate

/-- A pointwise real operation transfers a limit on the same complete domain. -/
theorem finiteFunctionLimitMap {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f g point value result : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g)
    (hD : F.domainValue g = F.domainValue f)
    (rawOp : M.Value → M.Value) (nativeOp : ℝ → ℝ)
    (hop : ∀ x : ℝ, rawOp (M.number (x : ℂ)) = M.number (nativeOp x : ℂ))
    (hresult : result = rawOp value)
    (hformula : ∀ input, M.mem input (F.domainValue f) →
      F.callValue g input = rawOp (F.callValue f input))
    (hcontinuous : Continuous nativeOp)
    (h : HasFiniteFunctionLimitValue M side f point value) :
    HasFiniteFunctionLimitValue M side g point result := by
  obtain ⟨p, l, hp, hl, ha, he⟩ := h
  refine ⟨p, nativeOp l, hp, ?_, ?_, ?_⟩
  · rw [hresult, hl, hop]
  · intro radius hradius
    obtain ⟨x, hx, hpositive, hnear⟩ := ha radius hradius
    exact ⟨x, hD ▸ hx, hpositive, hnear⟩
  · apply (finiteFunctionEpsilon_iff_tendsto side g hg p (nativeOp l)).mpr
    have hsource := (finiteFunctionEpsilon_iff_tendsto side f hf p l).mp he
    have hpointwise : observeRealFunction g =ᶠ[nhdsWithin p (finiteApproachSet M side f p)]
        (fun x => nativeOp (observeRealFunction f x)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have equation := hformula (M.number (x : ℂ)) hx.1
      rw [observeRealFunction_spec f hf x hx.1, hop] at equation
      unfold observeRealFunction
      rw [equation, observeRealValue_number]
      rfl
    have mapped := hcontinuous.continuousAt.tendsto.comp hsource
    have hset : finiteApproachSet M side g p = finiteApproachSet M side f p := by
      simp only [finiteApproachSet, hD]
    rw [hset]
    exact mapped.congr' hpointwise.symm

theorem finiteFunctionLimitMapTwo {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f g out point a b result : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g) (hout : RealFunctionValue M out)
    (hgD : F.domainValue g = F.domainValue f) (houtD : F.domainValue out = F.domainValue f)
    (rawOp : M.Value → M.Value → M.Value) (nativeOp : ℝ → ℝ → ℝ)
    (hop : ∀ x y : ℝ, rawOp (M.number (x : ℂ)) (M.number (y : ℂ)) = M.number (nativeOp x y : ℂ))
    (hresult : result = rawOp a b)
    (hformula : ∀ input, M.mem input (F.domainValue f) →
      F.callValue out input = rawOp (F.callValue f input) (F.callValue g input))
    (hcontinuous : Continuous (fun pair : ℝ × ℝ => nativeOp pair.1 pair.2))
    (ha : HasFiniteFunctionLimitValue M side f point a)
    (hb : HasFiniteFunctionLimitValue M side g point b) :
    HasFiniteFunctionLimitValue M side out point result := by
  obtain ⟨p, l, hp, hl, hacc, he⟩ := ha
  obtain ⟨q, k, hq, hk, _, he'⟩ := hb
  have hpq : p = q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  subst q
  refine ⟨p, nativeOp l k, hp, ?_, ?_, ?_⟩
  · rw [hresult, hl, hk, hop]
  · intro radius hradius
    obtain ⟨x, hx, hpositive, hnear⟩ := hacc radius hradius
    exact ⟨x, houtD ▸ hx, hpositive, hnear⟩
  · apply (finiteFunctionEpsilon_iff_tendsto side out hout p (nativeOp l k)).mpr
    have hsource := (finiteFunctionEpsilon_iff_tendsto side f hf p l).mp he
    have hother := (finiteFunctionEpsilon_iff_tendsto side g hg p k).mp he'
    have hgset : finiteApproachSet M side g p = finiteApproachSet M side f p := by
      simp only [finiteApproachSet, hgD]
    rw [hgset] at hother
    have hpointwise : observeRealFunction out =ᶠ[nhdsWithin p (finiteApproachSet M side f p)]
        (fun x => nativeOp (observeRealFunction f x) (observeRealFunction g x)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have equation := hformula (M.number (x : ℂ)) hx.1
      rw [observeRealFunction_spec f hf x hx.1,
        observeRealFunction_spec g hg x (hgD ▸ hx.1), hop] at equation
      unfold observeRealFunction
      rw [equation, observeRealValue_number]
      rfl
    have mapped := hcontinuous.continuousAt.tendsto.comp (hsource.prodMk_nhds hother)
    have hset : finiteApproachSet M side out p = finiteApproachSet M side f p := by
      simp only [finiteApproachSet, houtD]
    rw [hset]
    exact mapped.congr' hpointwise.symm

def infinityBaseFilter (direction : InfiniteLimitDirection) : Filter ℝ :=
  match direction with | .positive => atTop | .negative => atBot

def infiniteApproachFilter (M : Semantics.{u}) [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f : M.Value) : Filter ℝ :=
  infinityBaseFilter direction ⊓ principal {x | M.mem (M.number (x : ℂ)) (F.domainValue f)}

theorem eventually_infiniteApproach_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f : M.Value) (P : ℝ → Prop) :
    (∀ᶠ x in infiniteApproachFilter M direction f, P x) ↔
      ∃ bound : ℝ, ∀ input : ℝ, M.mem (M.number (input : ℂ)) (F.domainValue f) →
        infiniteBeyond direction bound input → P input := by
  cases direction with
  | positive =>
      rw [infiniteApproachFilter, infinityBaseFilter, eventually_inf_principal, eventually_atTop]
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨b, fun x hx hnear => hb x (le_of_lt hnear) hx⟩
      · rintro ⟨b, hb⟩
        refine ⟨b+1, fun x hx hdomain => hb x hdomain ?_⟩
        dsimp [infiniteBeyond]
        linarith
  | negative =>
      rw [infiniteApproachFilter, infinityBaseFilter, eventually_inf_principal, eventually_atBot]
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨b, fun x hx hnear => hb x (le_of_lt hnear) hx⟩
      · rintro ⟨b, hb⟩
        refine ⟨b-1, fun x hx hdomain => hb x hdomain ?_⟩
        dsimp [infiniteBeyond]
        linarith

theorem infiniteFunctionEpsilon_iff_tendsto {M : Semantics.{u}} [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f : M.Value) (hf : RealFunctionValue M f) (value : ℝ) :
    InfiniteFunctionEpsilonValue M direction f value ↔
      Tendsto (observeRealFunction f) (infiniteApproachFilter M direction f) (𝓝 value) := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro he epsilon hepsilon
    obtain ⟨bound, hcontrol⟩ := he epsilon hepsilon
    apply (eventually_infiniteApproach_iff direction f _).mpr
    refine ⟨bound, ?_⟩
    intro x hx hbeyond
    obtain ⟨y, hy, hestimate⟩ := hcontrol x hx hbeyond
    have observed : observeRealFunction f x = y := by
      unfold observeRealFunction
      rw [hy, observeRealValue_number]
    simpa only [observed, Real.dist_eq] using hestimate
  · intro he epsilon hepsilon
    obtain ⟨bound, hcontrol⟩ := (eventually_infiniteApproach_iff direction f _).mp (he epsilon hepsilon)
    refine ⟨bound, ?_⟩
    intro x hx hbeyond
    refine ⟨observeRealFunction f x, observeRealFunction_spec f hf x hx, ?_⟩
    simpa only [Real.dist_eq] using hcontrol x hx hbeyond

theorem infiniteFunctionLimitMap {M : Semantics.{u}} [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f g value result : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g)
    (hD : F.domainValue g = F.domainValue f)
    (rawOp : M.Value → M.Value) (nativeOp : ℝ → ℝ)
    (hop : ∀ x : ℝ, rawOp (M.number (x : ℂ)) = M.number (nativeOp x : ℂ))
    (hresult : result = rawOp value)
    (hformula : ∀ input, M.mem input (F.domainValue f) →
      F.callValue g input = rawOp (F.callValue f input))
    (hcontinuous : Continuous nativeOp)
    (h : HasInfiniteFunctionLimitValue M direction f value) :
    HasInfiniteFunctionLimitValue M direction g result := by
  obtain ⟨l, hl, ha, he⟩ := h
  refine ⟨nativeOp l, ?_, ?_, ?_⟩
  · rw [hresult, hl, hop]
  · intro bound
    obtain ⟨x, hx, hbeyond⟩ := ha bound
    exact ⟨x, hD ▸ hx, hbeyond⟩
  · apply (infiniteFunctionEpsilon_iff_tendsto direction g hg (nativeOp l)).mpr
    have hsource := (infiniteFunctionEpsilon_iff_tendsto direction f hf l).mp he
    have hpointwise : observeRealFunction g =ᶠ[infiniteApproachFilter M direction f]
        (fun x => nativeOp (observeRealFunction f x)) := by
      apply eventually_inf_principal.mpr
      apply Eventually.of_forall
      intro x hx
      have equation := hformula (M.number (x : ℂ)) hx
      rw [observeRealFunction_spec f hf x hx, hop] at equation
      unfold observeRealFunction
      rw [equation, observeRealValue_number]
      rfl
    have mapped := hcontinuous.continuousAt.tendsto.comp hsource
    have hfilter : infiniteApproachFilter M direction g = infiniteApproachFilter M direction f := by
      simp only [infiniteApproachFilter, hD]
    rw [hfilter]
    exact mapped.congr' hpointwise.symm

theorem infiniteFunctionLimitMapTwo {M : Semantics.{u}} [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f g out a b result : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g) (hout : RealFunctionValue M out)
    (hgD : F.domainValue g = F.domainValue f) (houtD : F.domainValue out = F.domainValue f)
    (rawOp : M.Value → M.Value → M.Value) (nativeOp : ℝ → ℝ → ℝ)
    (hop : ∀ x y : ℝ, rawOp (M.number (x : ℂ)) (M.number (y : ℂ)) = M.number (nativeOp x y : ℂ))
    (hresult : result = rawOp a b)
    (hformula : ∀ input, M.mem input (F.domainValue f) →
      F.callValue out input = rawOp (F.callValue f input) (F.callValue g input))
    (hcontinuous : Continuous (fun pair : ℝ × ℝ => nativeOp pair.1 pair.2))
    (ha : HasInfiniteFunctionLimitValue M direction f a)
    (hb : HasInfiniteFunctionLimitValue M direction g b) :
    HasInfiniteFunctionLimitValue M direction out result := by
  obtain ⟨l, hl, hacc, he⟩ := ha
  obtain ⟨k, hk, _, he'⟩ := hb
  refine ⟨nativeOp l k, ?_, ?_, ?_⟩
  · rw [hresult, hl, hk, hop]
  · intro bound
    obtain ⟨x, hx, hbeyond⟩ := hacc bound
    exact ⟨x, houtD ▸ hx, hbeyond⟩
  · apply (infiniteFunctionEpsilon_iff_tendsto direction out hout (nativeOp l k)).mpr
    have hsource := (infiniteFunctionEpsilon_iff_tendsto direction f hf l).mp he
    have hother := (infiniteFunctionEpsilon_iff_tendsto direction g hg k).mp he'
    have hgfilter : infiniteApproachFilter M direction g = infiniteApproachFilter M direction f := by
      simp only [infiniteApproachFilter, hgD]
    rw [hgfilter] at hother
    have hpointwise : observeRealFunction out =ᶠ[infiniteApproachFilter M direction f]
        (fun x => nativeOp (observeRealFunction f x) (observeRealFunction g x)) := by
      apply eventually_inf_principal.mpr
      apply Eventually.of_forall
      intro x hx
      have equation := hformula (M.number (x : ℂ)) hx
      rw [observeRealFunction_spec f hf x hx,
        observeRealFunction_spec g hg x (hgD ▸ hx), hop] at equation
      unfold observeRealFunction
      rw [equation, observeRealValue_number]
      rfl
    have mapped := hcontinuous.continuousAt.tendsto.comp (hsource.prodMk_nhds hother)
    have hfilter : infiniteApproachFilter M direction out = infiniteApproachFilter M direction f := by
      simp only [infiniteApproachFilter, houtD]
    rw [hfilter]
    exact mapped.congr' hpointwise.symm

end Litex


namespace Litex
open Filter
open scoped Topology

theorem finiteFunctionLimitDivide {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f g out point a b result : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g) (hout : RealFunctionValue M out)
    (hgD : F.domainValue g = F.domainValue f) (houtD : F.domainValue out = F.domainValue f)
    (hresult : result = M.divValue a b) (hbzero : b ≠ M.number 0)
    (hdenominator : ∀ input, M.mem input (F.domainValue f) → F.callValue g input ≠ M.number 0)
    (hformula : ∀ input, M.mem input (F.domainValue f) →
      F.callValue out input = M.divValue (F.callValue f input) (F.callValue g input))
    (ha : HasFiniteFunctionLimitValue M side f point a)
    (hb : HasFiniteFunctionLimitValue M side g point b) :
    HasFiniteFunctionLimitValue M side out point result := by
  obtain ⟨p, l, hp, hl, hacc, he⟩ := ha
  obtain ⟨q, k, hq, hk, _, he'⟩ := hb
  have hpq : p = q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  subst q
  have hkzero : k ≠ 0 := by
    intro hk0
    apply hbzero
    simpa only [hk0, Complex.ofReal_zero] using hk
  refine ⟨p, l/k, hp, ?_, ?_, ?_⟩
  · rw [hresult, hl, hk, M.div_numbers _ _ (Complex.ofReal_ne_zero.mpr hkzero), ← Complex.ofReal_div]
  · intro radius hradius
    obtain ⟨x, hx, hpositive, hnear⟩ := hacc radius hradius
    exact ⟨x, houtD ▸ hx, hpositive, hnear⟩
  · apply (finiteFunctionEpsilon_iff_tendsto side out hout p (l/k)).mpr
    have hsource := (finiteFunctionEpsilon_iff_tendsto side f hf p l).mp he
    have hother := (finiteFunctionEpsilon_iff_tendsto side g hg p k).mp he'
    have hgset : finiteApproachSet M side g p = finiteApproachSet M side f p := by
      simp only [finiteApproachSet, hgD]
    rw [hgset] at hother
    have hpointwise : observeRealFunction out =ᶠ[nhdsWithin p (finiteApproachSet M side f p)]
        (fun x => observeRealFunction f x / observeRealFunction g x) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hinputzero : observeRealFunction g x ≠ 0 := by
        intro hzero
        apply hdenominator (M.number (x : ℂ)) hx.1
        simpa only [hzero, Complex.ofReal_zero] using observeRealFunction_spec g hg x (hgD ▸ hx.1)
      have equation := hformula (M.number (x : ℂ)) hx.1
      rw [observeRealFunction_spec f hf x hx.1, observeRealFunction_spec g hg x (hgD ▸ hx.1),
        M.div_numbers _ _ (Complex.ofReal_ne_zero.mpr hinputzero), ← Complex.ofReal_div] at equation
      change observeRealValue (F.callValue out (M.number (x : ℂ))) = _
      rw [equation, observeRealValue_number]
    have mapped := hsource.div hother hkzero
    have hset : finiteApproachSet M side out p = finiteApproachSet M side f p := by
      simp only [finiteApproachSet, houtD]
    rw [hset]
    exact mapped.congr' hpointwise.symm

theorem infiniteFunctionLimitDivide {M : Semantics.{u}} [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f g out a b result : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g) (hout : RealFunctionValue M out)
    (hgD : F.domainValue g = F.domainValue f) (houtD : F.domainValue out = F.domainValue f)
    (hresult : result = M.divValue a b) (hbzero : b ≠ M.number 0)
    (hdenominator : ∀ input, M.mem input (F.domainValue f) → F.callValue g input ≠ M.number 0)
    (hformula : ∀ input, M.mem input (F.domainValue f) →
      F.callValue out input = M.divValue (F.callValue f input) (F.callValue g input))
    (ha : HasInfiniteFunctionLimitValue M direction f a)
    (hb : HasInfiniteFunctionLimitValue M direction g b) :
    HasInfiniteFunctionLimitValue M direction out result := by
  obtain ⟨l, hl, hacc, he⟩ := ha
  obtain ⟨k, hk, _, he'⟩ := hb
  have hkzero : k ≠ 0 := by
    intro hk0
    apply hbzero
    simpa only [hk0, Complex.ofReal_zero] using hk
  refine ⟨l/k, ?_, ?_, ?_⟩
  · rw [hresult, hl, hk, M.div_numbers _ _ (Complex.ofReal_ne_zero.mpr hkzero), ← Complex.ofReal_div]
  · intro bound
    obtain ⟨x, hx, hbeyond⟩ := hacc bound
    exact ⟨x, houtD ▸ hx, hbeyond⟩
  · apply (infiniteFunctionEpsilon_iff_tendsto direction out hout (l/k)).mpr
    have hsource := (infiniteFunctionEpsilon_iff_tendsto direction f hf l).mp he
    have hother := (infiniteFunctionEpsilon_iff_tendsto direction g hg k).mp he'
    have hgfilter : infiniteApproachFilter M direction g = infiniteApproachFilter M direction f := by
      simp only [infiniteApproachFilter, hgD]
    rw [hgfilter] at hother
    have hpointwise : observeRealFunction out =ᶠ[infiniteApproachFilter M direction f]
        (fun x => observeRealFunction f x / observeRealFunction g x) := by
      apply eventually_inf_principal.mpr
      apply Eventually.of_forall
      intro x hx
      have hinputzero : observeRealFunction g x ≠ 0 := by
        intro hzero
        apply hdenominator (M.number (x : ℂ)) hx
        simpa only [hzero, Complex.ofReal_zero] using observeRealFunction_spec g hg x (hgD ▸ hx)
      have equation := hformula (M.number (x : ℂ)) hx
      rw [observeRealFunction_spec f hf x hx, observeRealFunction_spec g hg x (hgD ▸ hx),
        M.div_numbers _ _ (Complex.ofReal_ne_zero.mpr hinputzero), ← Complex.ofReal_div] at equation
      change observeRealValue (F.callValue out (M.number (x : ℂ))) = _
      rw [equation, observeRealValue_number]
    have mapped := hsource.div hother hkzero
    have hfilter : infiniteApproachFilter M direction out = infiniteApproachFilter M direction f := by
      simp only [infiniteApproachFilter, houtD]
    rw [hfilter]
    exact mapped.congr' hpointwise.symm

end Litex


namespace Litex

theorem finiteFunctionEpsilonRestrictSide {M : Semantics.{u}} [FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (point value : ℝ)
    (h : FiniteFunctionEpsilonValue M .both f point value) :
    FiniteFunctionEpsilonValue M side f point value := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hcontrol⟩ := h epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro x hx hpositive hnear
  have hdist := finiteLimitDistance_eq_abs side point x hpositive
  apply hcontrol x hx
  · change 0 < |x-point|
    rw [← hdist]
    exact hpositive
  · change |x-point| < delta
    rw [← hdist]
    exact hnear

theorem finiteFunctionLimitRestrictSide {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f point value : M.Value) (domain : Obj (M := M) M.Value)
    (hf : RealFunctionValue M f) (hD : denote domain = F.domainValue f)
    (ha : ∀ radius : Obj (M := M) M.Value, In radius RPos →
      FiniteLimitAccumulationClauseValue M side (denote domain) point (denote radius))
    (h : HasFiniteFunctionLimitValue M .both f point value) :
    HasFiniteFunctionLimitValue M side f point value := by
  obtain ⟨p, l, hp, hl, _, he⟩ := h
  refine ⟨p, l, hp, hl, ?_, finiteFunctionEpsilonRestrictSide side f p l he⟩
  intro radius hradius
  have hm : M.mem (M.number (radius : ℂ)) (denote (RPos (M := M))) := numberInRPos radius hradius
  let r := semanticObject (M.number (radius : ℂ)) (M.member_isSet hm)
  obtain ⟨input, hmem, hpositive, hnear⟩ := ha r hm
  obtain ⟨signature, hfn, hreal, _⟩ := hf
  have hd : denote domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  obtain ⟨x, hx⟩ := (M.real_members _).mp (hreal _ (hd ▸ hmem))
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [← hx, ← hD]
    exact hmem
  · change RealLtValue M (M.number 0) (finiteLimitDistanceValue side point (denote input)) at hpositive
    rw [hp, hx, finiteLimitDistanceValue_numbers] at hpositive
    exact (realLtValue_numbers 0 _).mp hpositive
  · change RealLtValue M (finiteLimitDistanceValue side point (denote input)) (M.number (radius : ℂ)) at hnear
    rw [hp, hx, finiteLimitDistanceValue_numbers] at hnear
    exact (realLtValue_numbers _ radius).mp hnear

theorem finiteFunctionLimitFromSides {M : Semantics.{u}} [FunctionSemantics M]
    (f point value : M.Value)
    (hl : HasFiniteFunctionLimitValue M .left f point value)
    (hr : HasFiniteFunctionLimitValue M .right f point value) :
    HasFiniteFunctionLimitValue M .both f point value := by
  obtain ⟨p, l, hp, hlvalue, hacc, hleft⟩ := hl
  obtain ⟨q, r, hq, hrvalue, _, hright⟩ := hr
  have hpq : p = q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  have hlr : l = r := Complex.ofReal_injective (M.number_injective (hlvalue.symm.trans hrvalue))
  subst q
  subst r
  refine ⟨p, l, hp, hlvalue, ?_, ?_⟩
  · intro radius hradius
    obtain ⟨x, hx, hpositive, hnear⟩ := hacc radius hradius
    have hdist := finiteLimitDistance_eq_abs .left p x hpositive
    refine ⟨x, hx, ?_, ?_⟩
    · change 0 < |x-p|
      rw [← hdist]
      exact hpositive
    · change |x-p| < radius
      rw [← hdist]
      exact hnear
  · intro epsilon hepsilon
    obtain ⟨dl, hdl, hleft⟩ := hleft epsilon hepsilon
    obtain ⟨dr, hdr, hright⟩ := hright epsilon hepsilon
    refine ⟨Min.min dl dr, lt_min hdl hdr, ?_⟩
    intro x hx hpositive hnear
    have hne : x ≠ p := sub_ne_zero.mp (abs_pos.mp hpositive)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpos : 0 < finiteLimitDistance .left p x := by dsimp [finiteLimitDistance]; linarith
      have hdist := finiteLimitDistance_eq_abs .left p x hpos
      apply hleft x hx hpos
      rw [hdist]
      exact lt_of_lt_of_le hnear (min_le_left _ _)
    · have hpos : 0 < finiteLimitDistance .right p x := by dsimp [finiteLimitDistance]; linarith
      have hdist := finiteLimitDistance_eq_abs .right p x hpos
      apply hright x hx hpos
      rw [hdist]
      exact lt_of_lt_of_le hnear (min_le_right _ _)

theorem finiteFunctionLimitSidesDifferent {M : Semantics.{u}} [FunctionSemantics M]
    (f point a b : M.Value)
    (ha : HasFiniteFunctionLimitValue M .left f point a)
    (hb : HasFiniteFunctionLimitValue M .right f point b) (hne : a ≠ b) :
    ∀ value : M.Value, ¬ HasFiniteFunctionLimitValue M .both f point value := by
  intro value h
  obtain ⟨p, l, hp, hl, haccL, heL⟩ := ha
  obtain ⟨q, r, hq, hr, haccR, heR⟩ := hb
  obtain ⟨s, k, hs, _, _, he⟩ := h
  have hpq : p = q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  have hps : p = s := Complex.ofReal_injective (M.number_injective (hp.symm.trans hs))
  subst q
  subst s
  have hlk := finiteFunctionLimitUnique .left f p l k haccL heL
    (finiteFunctionEpsilonRestrictSide .left f p k he)
  have hrk := finiteFunctionLimitUnique .right f p r k haccR heR
    (finiteFunctionEpsilonRestrictSide .right f p k he)
  exact hne (hl.trans ((congrArg (fun z : ℝ => M.number (z : ℂ))
    (hlk.trans hrk.symm)).trans hr.symm))

end Litex


namespace Litex

/-- An epsilon ball with radius half a positive value stays positive. -/
theorem sequenceEpsilonBall_positive {M : Semantics.{u}} [SetSemantics M]
    (value : ℝ) (hv : 0 < value) (output : M.Value)
    (h : M.mem output (sequenceEpsilonBallValue (M.number (value : ℂ)) (M.number ((value/2 : ℝ) : ℂ)))) :
    M.mem output (denote (RPos (M := M))) := by
  have hreal := ((SetSemantics.sep_members _ _ _).mp h).1
  obtain ⟨y, hy⟩ := (M.real_members _).mp hreal
  rw [hy] at h ⊢
  have hclose := (sequenceEpsilonBall_numbers value (value/2) y).mp h
  have hpositive : 0 < y := by
    have := (abs_lt.mp hclose).1
    linarith
  exact numberInRPos y hpositive

/-- A ball with radius half the distance to zero excludes zero. -/
theorem sequenceEpsilonBall_nonzero {M : Semantics.{u}} [SetSemantics M]
    (value : ℝ) (hv : value ≠ 0) (output : M.Value)
    (h : M.mem output (sequenceEpsilonBallValue (M.number (value : ℂ)) (M.number ((|value|/2 : ℝ) : ℂ)))) :
    M.mem output (denote (RStar (M := M))) := by
  have hreal := ((SetSemantics.sep_members _ _ _).mp h).1
  obtain ⟨y, hy⟩ := (M.real_members _).mp hreal
  rw [hy] at h ⊢
  have hclose := (sequenceEpsilonBall_numbers value (|value|/2) y).mp h
  have hnonzero : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_sub, abs_neg] at hclose
    have := abs_pos.mpr hv
    linarith
  exact inRStar_intro (number (M := M) (y : ℂ)) (NativeBridge.numberInR y)
    (NativeBridge.numberNonzero (y : ℂ) (Complex.ofReal_ne_zero.mpr hnonzero))

theorem preimageValue_mono {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f) (P Q : M.Value → Prop)
    (h : ∀ y, P y → Q y) :
    ∀ x, M.mem x (F.preimageValue f P) → M.mem x (F.preimageValue f Q) := by
  obtain ⟨signature, hfn, _, _⟩ := hf
  intro x hx
  have hx := (F.preimage_mem_iff P signature.domain_isSet hfn).mp hx
  exact (F.preimage_mem_iff Q signature.domain_isSet hfn).mpr ⟨hx.1, h _ hx.2⟩

def FiniteLimitEventualClauseValue (M : Semantics.{u}) [FunctionSemantics M]
    (side : FiniteLimitSide) (f domain point target : M.Value) : Prop :=
  ∃ delta : Obj (M := M) M.Value, ∃ _ : In delta RPos,
    ∀ input, M.mem input (finiteLimitNeighborhoodValue side domain point (denote delta)) →
      M.mem input (FunctionSemantics.preimageValue f (fun y => M.mem y target))

def InfiniteLimitEventualClauseValue (M : Semantics.{u}) [FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f domain target : M.Value) : Prop :=
  ∃ bound : Obj (M := M) M.Value, ∃ _ : In bound R,
    ∀ input, M.mem input (infiniteLimitTailValue direction domain (denote bound)) →
      M.mem input (FunctionSemantics.preimageValue f (fun y => M.mem y target))

theorem finiteFunctionLimitEventuallyPositive {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) (domain : Obj (M := M) δ)
    (hf : RealFunctionValue M (denote f)) (hD : denote domain = F.domainValue (denote f))
    (h : HasFiniteFunctionLimit side f point value) (hv : Lt (number 0) value) :
    FiniteLimitEventualClauseValue M side (denote f) (denote domain) (denote point) (denote (RPos (M := M))) := by
  obtain ⟨l, hl, hlpos⟩ := NativeBridge.realWitnessOfPositive value hv
  have he : M.mem (M.number ((l/2 : ℝ) : ℂ)) (denote (RPos (M := M))) := numberInRPos (l/2) (by linarith)
  let epsilon := semanticObject (M.number ((l/2 : ℝ) : ℂ)) (M.member_isSet he)
  obtain ⟨delta, hdelta, hcontrol⟩ := finiteFunctionLimitControl side f point value domain hf hD h epsilon he
  refine ⟨delta, hdelta, ?_⟩
  intro input hx
  apply preimageValue_mono (denote f) hf _ _ _ input (hcontrol input hx)
  intro output houtput
  rw [hl] at houtput
  exact sequenceEpsilonBall_positive l hlpos output houtput

theorem finiteFunctionLimitEventuallyNonzero {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (value : Obj (M := M) γ) (domain : Obj (M := M) δ)
    (hf : RealFunctionValue M (denote f)) (hD : denote domain = F.domainValue (denote f))
    (h : HasFiniteFunctionLimit side f point value) (hv : ¬ Same value (number 0)) :
    FiniteLimitEventualClauseValue M side (denote f) (denote domain) (denote point) (denote (RStar (M := M))) := by
  obtain ⟨p, l, hp, hl, ha, hc⟩ := h
  have hlzero : l ≠ 0 := by
    intro hzero
    apply hv
    change denote value = M.number 0
    simpa only [hzero, Complex.ofReal_zero] using hl
  have he : M.mem (M.number ((|l|/2 : ℝ) : ℂ)) (denote (RPos (M := M))) :=
    numberInRPos (|l|/2) (by have := abs_pos.mpr hlzero; linarith)
  let epsilon := semanticObject (M.number ((|l|/2 : ℝ) : ℂ)) (M.member_isSet he)
  obtain ⟨delta, hdelta, hcontrol⟩ := finiteFunctionLimitControl side f point value domain hf hD
    ⟨p, l, hp, hl, ha, hc⟩ epsilon he
  refine ⟨delta, hdelta, ?_⟩
  intro input hx
  apply preimageValue_mono (denote f) hf _ _ _ input (hcontrol input hx)
  intro output houtput
  rw [hl] at houtput
  exact sequenceEpsilonBall_nonzero l hlzero output houtput

theorem infiniteFunctionLimitEventuallyPositive {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M γ] [Representation M δ]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α) (value : Obj (M := M) γ) (domain : Obj (M := M) δ)
    (hf : RealFunctionValue M (denote f)) (hD : denote domain = F.domainValue (denote f))
    (h : HasInfiniteFunctionLimit direction f value) (hv : Lt (number 0) value) :
    InfiniteLimitEventualClauseValue M direction (denote f) (denote domain) (denote (RPos (M := M))) := by
  obtain ⟨l, hl, hlpos⟩ := NativeBridge.realWitnessOfPositive value hv
  have he : M.mem (M.number ((l/2 : ℝ) : ℂ)) (denote (RPos (M := M))) := numberInRPos (l/2) (by linarith)
  let epsilon := semanticObject (M.number ((l/2 : ℝ) : ℂ)) (M.member_isSet he)
  obtain ⟨delta, hdelta, hcontrol⟩ := infiniteFunctionLimitControl direction f value domain hf hD h epsilon he
  refine ⟨delta, hdelta, ?_⟩
  intro input hx
  apply preimageValue_mono (denote f) hf _ _ _ input (hcontrol input hx)
  intro output houtput
  rw [hl] at houtput
  exact sequenceEpsilonBall_positive l hlpos output houtput

theorem infiniteFunctionLimitEventuallyNonzero {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M γ] [Representation M δ]
    (direction : InfiniteLimitDirection) (f : Obj (M := M) α) (value : Obj (M := M) γ) (domain : Obj (M := M) δ)
    (hf : RealFunctionValue M (denote f)) (hD : denote domain = F.domainValue (denote f))
    (h : HasInfiniteFunctionLimit direction f value) (hv : ¬ Same value (number 0)) :
    InfiniteLimitEventualClauseValue M direction (denote f) (denote domain) (denote (RStar (M := M))) := by
  obtain ⟨l, hl, ha, hc⟩ := h
  have hlzero : l ≠ 0 := by
    intro hzero
    apply hv
    change denote value = M.number 0
    simpa only [hzero, Complex.ofReal_zero] using hl
  have he : M.mem (M.number ((|l|/2 : ℝ) : ℂ)) (denote (RPos (M := M))) :=
    numberInRPos (|l|/2) (by have := abs_pos.mpr hlzero; linarith)
  let epsilon := semanticObject (M.number ((|l|/2 : ℝ) : ℂ)) (M.member_isSet he)
  obtain ⟨delta, hdelta, hcontrol⟩ := infiniteFunctionLimitControl direction f value domain hf hD
    ⟨l, hl, ha, hc⟩ epsilon he
  refine ⟨delta, hdelta, ?_⟩
  intro input hx
  apply preimageValue_mono (denote f) hf _ _ _ input (hcontrol input hx)
  intro output houtput
  rw [hl] at houtput
  exact sequenceEpsilonBall_nonzero l hlzero output houtput

end Litex


namespace Litex

def RealLeValue (M : Semantics.{u}) (a b : M.Value) : Prop :=
  ∃ r s : ℝ, a = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r ≤ s

theorem realLeValue_numbers {M : Semantics.{u}} (a b : ℝ) :
    RealLeValue M (M.number (a : ℂ)) (M.number (b : ℂ)) ↔ a ≤ b := by
  constructor
  · rintro ⟨r, s, hr, hs, h⟩
    have har : a = r := Complex.ofReal_injective (M.number_injective hr)
    have hbs : b = s := Complex.ofReal_injective (M.number_injective hs)
    simpa only [har, hbs] using h
  · exact fun h => ⟨a, b, rfl, rfl, h⟩

theorem finiteLimitNeighborhood_numbers_iff {M : Semantics.{u}} [SetSemantics M]
    (side : FiniteLimitSide) (domain : M.Value) (point radius input : ℝ) :
    M.mem (M.number (input : ℂ)) (finiteLimitNeighborhoodValue side domain
      (M.number (point : ℂ)) (M.number (radius : ℂ))) ↔
      M.mem (M.number (input : ℂ)) domain ∧ 0 < finiteLimitDistance side point input ∧
        finiteLimitDistance side point input < radius := by
  rw [finiteLimitNeighborhoodValue, SetSemantics.sep_members]
  simp only [finiteLimitDistanceValue_numbers]
  constructor
  · rintro ⟨hx, _, hp, hn⟩
    exact ⟨hx, (realLtValue_numbers 0 _).mp hp, (realLtValue_numbers _ radius).mp hn⟩
  · rintro ⟨hx, hp, hn⟩
    exact ⟨hx, hx, (realLtValue_numbers 0 _).mpr hp, (realLtValue_numbers _ radius).mpr hn⟩

theorem infiniteLimitTail_numbers_iff {M : Semantics.{u}} [SetSemantics M]
    (direction : InfiniteLimitDirection) (domain : M.Value) (bound input : ℝ) :
    M.mem (M.number (input : ℂ)) (infiniteLimitTailValue direction domain (M.number (bound : ℂ))) ↔
      M.mem (M.number (input : ℂ)) domain ∧ infiniteBeyond direction bound input := by
  rw [infiniteLimitTailValue, SetSemantics.sep_members]
  simp only [infiniteBeyondValue_numbers]
  exact ⟨fun ⟨hx, _, hn⟩ => ⟨hx, hn⟩, fun ⟨hx, hn⟩ => ⟨hx, hx, hn⟩⟩

theorem finiteFunctionLimitCompare {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (side : FiniteLimitSide) (f g point a b domain : M.Value)
    (radius : Obj (M := M) α) (hradius : In radius RPos)
    (hD : domain = F.domainValue f) (hgD : F.domainValue g = F.domainValue f)
    (ha : HasFiniteFunctionLimitValue M side f point a)
    (hb : HasFiniteFunctionLimitValue M side g point b)
    (hlocal : ∀ input, M.mem input (finiteLimitNeighborhoodValue side domain point (denote radius)) →
      RealLeValue M (F.callValue f input) (F.callValue g input)) :
    RealLeValue M a b := by
  obtain ⟨p, l, hp, hl, hacc, he⟩ := ha
  obtain ⟨q, k, hq, hk, _, he'⟩ := hb
  have hpq : p = q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  subst q
  refine ⟨l, k, hl, hk, ?_⟩
  by_contra hnot
  have hkl : k < l := lt_of_not_ge hnot
  let epsilon := (l-k)/3
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  obtain ⟨dl, hdl, hleft⟩ := he epsilon hepsilon
  obtain ⟨dr, hdr, hright⟩ := he' epsilon hepsilon
  obtain ⟨r, hr, hrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
  obtain ⟨x, hx, hpositive, hnear⟩ := hacc (Min.min r (Min.min dl dr)) (lt_min hrpos (lt_min hdl hdr))
  have hlocalx : M.mem (M.number (x : ℂ)) (finiteLimitNeighborhoodValue side domain point (denote radius)) := by
    rw [hp, hr]
    apply (finiteLimitNeighborhood_numbers_iff side domain p r x).mpr
    exact ⟨hD ▸ hx, hpositive, lt_of_lt_of_le hnear (min_le_left _ _)⟩
  have hinner := lt_of_lt_of_le hnear (min_le_right r (Min.min dl dr))
  obtain ⟨y, hy, hyl⟩ := hleft x hx hpositive (lt_of_lt_of_le hinner (min_le_left _ _))
  obtain ⟨z, hz, hzk⟩ := hright x (hgD ▸ hx) hpositive (lt_of_lt_of_le hinner (min_le_right _ _))
  have horder := hlocal _ hlocalx
  rw [hy, hz] at horder
  have hyz := (realLeValue_numbers y z).mp horder
  have hylower := (abs_lt.mp hyl).1
  have hzkupper := (abs_lt.mp hzk).2
  dsimp [epsilon] at hylower hzkupper
  linarith

theorem infiniteFunctionLimitCompare {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (direction : InfiniteLimitDirection) (f g a b domain : M.Value)
    (bound : Obj (M := M) α) (hbound : In bound R)
    (hD : domain = F.domainValue f) (hgD : F.domainValue g = F.domainValue f)
    (ha : HasInfiniteFunctionLimitValue M direction f a)
    (hb : HasInfiniteFunctionLimitValue M direction g b)
    (hlocal : ∀ input, M.mem input (infiniteLimitTailValue direction domain (denote bound)) →
      RealLeValue M (F.callValue f input) (F.callValue g input)) :
    RealLeValue M a b := by
  obtain ⟨l, hl, hacc, he⟩ := ha
  obtain ⟨k, hk, _, he'⟩ := hb
  refine ⟨l, k, hl, hk, ?_⟩
  by_contra hnot
  have hkl : k < l := lt_of_not_ge hnot
  let epsilon := (l-k)/3
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  obtain ⟨dl, hleft⟩ := he epsilon hepsilon
  obtain ⟨dr, hright⟩ := he' epsilon hepsilon
  obtain ⟨r, hr⟩ := (M.real_members _).mp hbound
  let cutoff := commonInfinityThreshold direction r (commonInfinityThreshold direction dl dr)
  obtain ⟨x, hx, hbeyond⟩ := hacc cutoff
  have houter := infiniteBeyond_common direction r (commonInfinityThreshold direction dl dr) x hbeyond
  have hinner := infiniteBeyond_common direction dl dr x houter.2
  have hlocalx : M.mem (M.number (x : ℂ)) (infiniteLimitTailValue direction domain (denote bound)) := by
    rw [hr]
    exact (infiniteLimitTail_numbers_iff direction domain r x).mpr ⟨hD ▸ hx,houter.1⟩
  obtain ⟨y, hy, hyl⟩ := hleft x hx hinner.1
  obtain ⟨z, hz, hzk⟩ := hright x (hgD ▸ hx) hinner.2
  have horder := hlocal _ hlocalx
  rw [hy, hz] at horder
  have hyz := (realLeValue_numbers y z).mp horder
  have hylower := (abs_lt.mp hyl).1
  have hzkupper := (abs_lt.mp hzk).2
  dsimp [epsilon] at hylower hzkupper
  linarith

end Litex


namespace Litex

theorem finiteFunctionAccumulationFromClause {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f point domain : M.Value) (p : ℝ)
    (hf : RealFunctionValue M f) (hD : domain = F.domainValue f) (hp : point = M.number (p : ℂ))
    (ha : ∀ radius : Obj (M := M) M.Value, In radius RPos →
      FiniteLimitAccumulationClauseValue M side domain point (denote radius)) :
    FiniteFunctionAccumulationValue M side f p := by
  intro radius hradius
  have hm : M.mem (M.number (radius : ℂ)) (denote (RPos (M := M))) := numberInRPos radius hradius
  let r := semanticObject (M.number (radius : ℂ)) (M.member_isSet hm)
  obtain ⟨input, hmem, hpositive, hnear⟩ := ha r hm
  obtain ⟨signature, hfn, hreal, _⟩ := hf
  have hd : domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  obtain ⟨x, hx⟩ := (M.real_members _).mp (hreal _ (hd ▸ hmem))
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [← hx, ← hD]; exact hmem
  · change RealLtValue M (M.number 0) (finiteLimitDistanceValue side point (denote input)) at hpositive
    rw [hp, hx, finiteLimitDistanceValue_numbers] at hpositive
    exact (realLtValue_numbers 0 _).mp hpositive
  · change RealLtValue M (finiteLimitDistanceValue side point (denote input)) (M.number (radius : ℂ)) at hnear
    rw [hp, hx, finiteLimitDistanceValue_numbers] at hnear
    exact (realLtValue_numbers _ radius).mp hnear

theorem infiniteFunctionAccumulationFromClause {M : Semantics.{u}} [F : FunctionSemantics M]
    (direction : InfiniteLimitDirection) (f domain : M.Value)
    (hf : RealFunctionValue M f) (hD : domain = F.domainValue f)
    (ha : ∀ bound : Obj (M := M) M.Value, In bound R →
      InfiniteLimitAccumulationClauseValue M direction domain (denote bound)) :
    InfiniteFunctionAccumulationValue M direction f := by
  intro bound
  have hm : M.mem (M.number (bound : ℂ)) (denote (R (M := M))) := NativeBridge.numberInR bound
  let b := semanticObject (M.number (bound : ℂ)) (M.member_isSet hm)
  obtain ⟨input, hmem, hbeyond⟩ := ha b hm
  obtain ⟨signature, hfn, hreal, _⟩ := hf
  have hd : domain = signature.domain := hD.trans (F.domainValue_eq signature.domain_isSet hfn)
  obtain ⟨x, hx⟩ := (M.real_members _).mp (hreal _ (hd ▸ hmem))
  refine ⟨x, ?_, ?_⟩
  · rw [← hx, ← hD]; exact hmem
  · change infiniteBeyondValue M direction (M.number (bound : ℂ)) (denote input) at hbeyond
    rw [hx] at hbeyond
    exact (infiniteBeyondValue_numbers direction bound x).mp hbeyond

theorem finiteFunctionLimitLocalEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (side : FiniteLimitSide) (f g point value domain : M.Value)
    (radius : Obj (M := M) α) (hradius : In radius RPos)
    (hg : RealFunctionValue M g) (hD : domain = F.domainValue g)
    (h : HasFiniteFunctionLimitValue M side f point value)
    (ha : ∀ r : Obj (M := M) M.Value, In r RPos →
      FiniteLimitAccumulationClauseValue M side domain point (denote r))
    (hsubset : ∀ input, M.mem input (finiteLimitNeighborhoodValue side domain point (denote radius)) →
      M.mem input (F.domainValue f))
    (heq : ∀ input, M.mem input (finiteLimitNeighborhoodValue side domain point (denote radius)) →
      F.callValue g input = F.callValue f input) :
    HasFiniteFunctionLimitValue M side g point value := by
  obtain ⟨p, l, hp, hl, _, he⟩ := h
  refine ⟨p,l,hp,hl,finiteFunctionAccumulationFromClause side g point domain p hg hD hp ha,?_⟩
  intro epsilon hepsilon
  obtain ⟨d,hd,hcontrol⟩ := he epsilon hepsilon
  obtain ⟨r,hr,hrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
  refine ⟨Min.min d r,lt_min hd hrpos,?_⟩
  intro x hx hpositive hnear
  have hlocal : M.mem (M.number (x : ℂ)) (finiteLimitNeighborhoodValue side domain point (denote radius)) := by
    rw [hp,hr]
    exact (finiteLimitNeighborhood_numbers_iff side domain p r x).mpr
      ⟨hD ▸ hx,hpositive,lt_of_lt_of_le hnear (min_le_right _ _)⟩
  obtain ⟨y,hy,hyl⟩ := hcontrol x (hsubset _ hlocal) hpositive
    (lt_of_lt_of_le hnear (min_le_left _ _))
  exact ⟨y,(heq _ hlocal).trans hy,hyl⟩

theorem infiniteFunctionLimitLocalEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (direction : InfiniteLimitDirection) (f g value domain : M.Value)
    (bound : Obj (M := M) α) (hbound : In bound R)
    (hg : RealFunctionValue M g) (hD : domain = F.domainValue g)
    (h : HasInfiniteFunctionLimitValue M direction f value)
    (ha : ∀ b : Obj (M := M) M.Value, In b R →
      InfiniteLimitAccumulationClauseValue M direction domain (denote b))
    (hsubset : ∀ input, M.mem input (infiniteLimitTailValue direction domain (denote bound)) →
      M.mem input (F.domainValue f))
    (heq : ∀ input, M.mem input (infiniteLimitTailValue direction domain (denote bound)) →
      F.callValue g input = F.callValue f input) :
    HasInfiniteFunctionLimitValue M direction g value := by
  obtain ⟨l,hl,_,he⟩ := h
  refine ⟨l,hl,infiniteFunctionAccumulationFromClause direction g domain hg hD ha,?_⟩
  intro epsilon hepsilon
  obtain ⟨d,hcontrol⟩ := he epsilon hepsilon
  obtain ⟨r,hr⟩ := (M.real_members _).mp hbound
  refine ⟨commonInfinityThreshold direction d r,?_⟩
  intro x hx hbeyond
  have hcommon := infiniteBeyond_common direction d r x hbeyond
  have hlocal : M.mem (M.number (x : ℂ)) (infiniteLimitTailValue direction domain (denote bound)) := by
    rw [hr]
    exact (infiniteLimitTail_numbers_iff direction domain r x).mpr ⟨hD ▸ hx,hcommon.2⟩
  obtain ⟨y,hy,hyl⟩ := hcontrol x (hsubset _ hlocal) hcommon.1
  exact ⟨y,(heq _ hlocal).trans hy,hyl⟩

end Litex


namespace Litex

theorem finiteFunctionLimitSqueeze {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (side : FiniteLimitSide) (f middle upper point value domain : M.Value)
    (radius : Obj (M := M) α) (hradius : In radius RPos)
    (hmiddle : RealFunctionValue M middle)
    (hD : domain = F.domainValue f) (hmD : F.domainValue middle = F.domainValue f)
    (huD : F.domainValue upper = F.domainValue f)
    (hf : HasFiniteFunctionLimitValue M side f point value)
    (hu : HasFiniteFunctionLimitValue M side upper point value)
    (hlocal : ∀ input, M.mem input (finiteLimitNeighborhoodValue side domain point (denote radius)) →
      RealLeValue M (F.callValue f input) (F.callValue middle input) ∧
      RealLeValue M (F.callValue middle input) (F.callValue upper input)) :
    HasFiniteFunctionLimitValue M side middle point value := by
  obtain ⟨p,l,hp,hl,hacc,he⟩ := hf
  obtain ⟨q,k,hq,hk,_,he'⟩ := hu
  have hpq : p=q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  have hlk : l=k := Complex.ofReal_injective (M.number_injective (hl.symm.trans hk))
  subst q; subst k
  refine ⟨p,l,hp,hl,?_,?_⟩
  · intro r hr
    obtain ⟨x,hx,hpos,hnear⟩ := hacc r hr
    exact ⟨x,hmD ▸ hx,hpos,hnear⟩
  · intro epsilon hepsilon
    obtain ⟨dl,hdl,hleft⟩ := he epsilon hepsilon
    obtain ⟨du,hdu,hright⟩ := he' epsilon hepsilon
    obtain ⟨r,hr,hrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
    refine ⟨Min.min r (Min.min dl du),lt_min hrpos (lt_min hdl hdu),?_⟩
    intro x hx hpositive hnear
    have hxF : M.mem (M.number (x : ℂ)) (F.domainValue f) := hmD ▸ hx
    have hlocalx : M.mem (M.number (x : ℂ)) (finiteLimitNeighborhoodValue side domain point (denote radius)) := by
      rw [hp,hr]
      exact (finiteLimitNeighborhood_numbers_iff side domain p r x).mpr
        ⟨hD ▸ hxF,hpositive,lt_of_lt_of_le hnear (min_le_left _ _)⟩
    have hinner := lt_of_lt_of_le hnear (min_le_right r (Min.min dl du))
    obtain ⟨yl,hyl,hlclose⟩ := hleft x hxF hpositive (lt_of_lt_of_le hinner (min_le_left _ _))
    obtain ⟨yu,hyu,huclose⟩ := hright x (huD ▸ hxF) hpositive (lt_of_lt_of_le hinner (min_le_right _ _))
    let ym := observeRealFunction middle x
    have hym : F.callValue middle (M.number (x : ℂ)) = M.number (ym : ℂ) := observeRealFunction_spec middle hmiddle x hx
    have horder := hlocal _ hlocalx
    rw [hyl,hym,hyu] at horder
    have hlm := (realLeValue_numbers yl ym).mp horder.1
    have hmu := (realLeValue_numbers ym yu).mp horder.2
    refine ⟨ym,hym,abs_lt.mpr ⟨?_,?_⟩⟩
    · have := (abs_lt.mp hlclose).1; linarith
    · have := (abs_lt.mp huclose).2; linarith

theorem infiniteFunctionLimitSqueeze {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (direction : InfiniteLimitDirection) (f middle upper value domain : M.Value)
    (bound : Obj (M := M) α) (hbound : In bound R)
    (hmiddle : RealFunctionValue M middle)
    (hD : domain = F.domainValue f) (hmD : F.domainValue middle = F.domainValue f)
    (huD : F.domainValue upper = F.domainValue f)
    (hf : HasInfiniteFunctionLimitValue M direction f value)
    (hu : HasInfiniteFunctionLimitValue M direction upper value)
    (hlocal : ∀ input, M.mem input (infiniteLimitTailValue direction domain (denote bound)) →
      RealLeValue M (F.callValue f input) (F.callValue middle input) ∧
      RealLeValue M (F.callValue middle input) (F.callValue upper input)) :
    HasInfiniteFunctionLimitValue M direction middle value := by
  obtain ⟨l,hl,hacc,he⟩ := hf
  obtain ⟨k,hk,_,he'⟩ := hu
  have hlk : l=k := Complex.ofReal_injective (M.number_injective (hl.symm.trans hk))
  subst k
  refine ⟨l,hl,?_,?_⟩
  · intro b
    obtain ⟨x,hx,hbeyond⟩ := hacc b
    exact ⟨x,hmD ▸ hx,hbeyond⟩
  · intro epsilon hepsilon
    obtain ⟨dl,hleft⟩ := he epsilon hepsilon
    obtain ⟨du,hright⟩ := he' epsilon hepsilon
    obtain ⟨r,hr⟩ := (M.real_members _).mp hbound
    refine ⟨commonInfinityThreshold direction r (commonInfinityThreshold direction dl du),?_⟩
    intro x hx hbeyond
    have hxF : M.mem (M.number (x : ℂ)) (F.domainValue f) := hmD ▸ hx
    have houter := infiniteBeyond_common direction r (commonInfinityThreshold direction dl du) x hbeyond
    have hinner := infiniteBeyond_common direction dl du x houter.2
    have hlocalx : M.mem (M.number (x : ℂ)) (infiniteLimitTailValue direction domain (denote bound)) := by
      rw [hr]
      exact (infiniteLimitTail_numbers_iff direction domain r x).mpr ⟨hD ▸ hxF,houter.1⟩
    obtain ⟨yl,hyl,hlclose⟩ := hleft x hxF hinner.1
    obtain ⟨yu,hyu,huclose⟩ := hright x (huD ▸ hxF) hinner.2
    let ym := observeRealFunction middle x
    have hym : F.callValue middle (M.number (x : ℂ)) = M.number (ym : ℂ) := observeRealFunction_spec middle hmiddle x hx
    have horder := hlocal _ hlocalx
    rw [hyl,hym,hyu] at horder
    have hlm := (realLeValue_numbers yl ym).mp horder.1
    have hmu := (realLeValue_numbers ym yu).mp horder.2
    refine ⟨ym,hym,abs_lt.mpr ⟨?_,?_⟩⟩
    · have := (abs_lt.mp hlclose).1; linarith
    · have := (abs_lt.mp huclose).2; linarith

end Litex

namespace Litex
theorem sequenceStrictOrderWeak {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (reverse : Bool)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (h : SequenceOrderValue M true reverse a) :
    SequenceOrderValue M false reverse a := by
  intro m hm n hn hmn
  obtain ⟨r,s,hr,hs,hrs⟩ := hmn
  change r ≤ s at hrs
  rcases lt_or_eq_of_le hrs with hlt | heq
  · obtain ⟨p,q,hp,hq,hpq⟩ := h m hm n hn ⟨r,s,hr,hs,hlt⟩
    exact ⟨p,q,hp,hq,le_of_lt hpq⟩
  · have hsame : m = n := hr.trans ((congrArg (fun t : ℝ => M.number (t : ℂ)) heq).trans hs.symm)
    rw [← hsame]
    obtain ⟨p,hp⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hf hm)
    cases reverse <;> exact ⟨p,p,hp,hp,le_rfl⟩

theorem sequenceBoundedFromPointwise {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (lower : Obj (M := M) β) (upper : Obj (M := M) γ)
    (hf : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hl : In lower R) (hu : In upper R)
    (h : ∀ n, M.mem n (denote (NPos (M := M))) →
      RealLeValue M (denote lower) (F.callValue (denote a) n) ∧
      RealLeValue M (F.callValue (denote a) n) (denote upper)) :
    SequenceBounded a := by
  constructor
  · refine ⟨semanticObject (denote lower) (isSet lower),hl,?_⟩
    intro y hy
    obtain ⟨n,hn,rfl⟩ := (F.range_mem_iff (isSet (R (M := M))) hf).mp hy
    exact (h n hn).1
  · refine ⟨semanticObject (denote upper) (isSet upper),hu,?_⟩
    intro y hy
    obtain ⟨n,hn,rfl⟩ := (F.range_mem_iff (isSet (R (M := M))) hf).mp hy
    exact (h n hn).2
end Litex

-- Real sequence observations preserve the positive-indexed epsilon contracts.
open Filter
open scoped Topology
namespace Litex
noncomputable def observeRealSequence {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (n : ℕ) : ℝ :=
  observeRealValue (F.callValue a (M.number (n : ℂ)))

theorem observeRealSequence_spec {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (n : ℕ) (hn : 0<n)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M))))) :
    F.callValue a (M.number (n : ℂ)) = M.number (observeRealSequence a n : ℂ) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp
    (F.call_mem _ _ _ _ hf (numberInNPosOfEq (n : ℂ) n rfl hn))
  change F.callValue a (M.number (n : ℂ)) = M.number (r : ℂ) at hr
  change F.callValue a (M.number (n : ℂ)) =
    M.number (observeRealValue (F.callValue a (M.number (n : ℂ))) : ℂ)
  rw [hr,observeRealValue_number]

theorem sequenceLimit_iff_tendsto {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (value : ℝ)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M))))) :
    HasSequenceLimitValue M a (M.number (value : ℂ)) ↔
      Tendsto (observeRealSequence a) atTop (𝓝 value) := by
  constructor
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro epsilon hepsilon
    obtain ⟨cutoff,hcut,htail⟩ := h (M.number (epsilon : ℂ)) (numberInRPos epsilon hepsilon)
    let cut := NativeBridge.asNat cutoff (inNPos_natural cutoff hcut)
    refine ⟨cut+1,?_⟩
    intro n hn
    have hnpos : 0<n := by omega
    have horder : cut≤n := by omega
    obtain ⟨r,hr,hdist⟩ := sequenceLimitAtIndex a value epsilon cutoff n hnpos hf hcut horder htail
    have heq : observeRealSequence a n=r := by
      unfold observeRealSequence
      rw [hr,observeRealValue_number]
    simpa only [Real.dist_eq,heq] using hdist
  · intro h epsilon hepsilon
    let e : Obj (M := M) M.Value := semanticObject epsilon (M.member_isSet hepsilon)
    have heR : In e R := inRPos_real e hepsilon
    let delta := NativeBridge.asReal e heR
    have hevalue : epsilon=M.number (delta : ℂ) := NativeBridge.asReal_spec e heR
    have hd : 0<delta :=
      (NativeBridge.lt_iff_ofDenoteReal (number (M := M) 0) e 0 delta rfl hevalue).mp
        (inRPos_positive e hepsilon)
    obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.mp h) delta hd
    let cut := N+1
    have hcut : 0<cut := by dsimp [cut];omega
    have hcutmem := numberInNPosOfEq (M := M) (cut : ℂ) cut rfl hcut
    let cutoff : Obj (M := M) M.Value :=
      semanticObject (M.number (cut : ℂ)) (M.member_isSet hcutmem)
    refine ⟨cutoff,hcutmem,?_⟩
    intro index htail
    obtain ⟨hindex,_,r,s,hr,hs,hrs⟩ := (F.sep_members _ _ _).mp htail
    obtain ⟨n,hn⟩ := (M.natural_members index).mp
      ((F.sep_members _ _ _).mp hindex).1
    change M.number (cut : ℂ)=M.number (r : ℂ) at hr
    have hrcut : (cut : ℝ)=r :=
      Complex.ofReal_injective (M.number_injective (by simpa only [Complex.ofReal_natCast] using hr))
    have hsindex : (n : ℝ)=s :=
      Complex.ofReal_injective (M.number_injective (by simpa only [Complex.ofReal_natCast] using hn.symm.trans hs))
    have hcutn : cut≤n := by exact_mod_cast (hrcut ▸ hsindex ▸ hrs)
    have hnpos : 0<n := by omega
    have hNn : N≤n := by dsimp [cut] at hcutn;omega
    have hdist : |observeRealSequence a n-value|<delta := by
      simpa only [Real.dist_eq] using hN n hNn
    apply (F.preimage_mem_iff
      (fun y => M.mem y (sequenceEpsilonBallValue (M.number (value : ℂ)) epsilon))
      (isSet (NPos (M := M))) hf).mpr
    refine ⟨hindex,?_⟩
    rw [hn,observeRealSequence_spec a n hnpos hf]
    apply (F.sep_members _ _ _).mpr
    have hreal : M.mem (M.number (observeRealSequence a n : ℂ)) (denote (R (M := M))) :=
      (M.real_members _).mpr ⟨_,rfl⟩
    refine ⟨hreal,hreal,|observeRealSequence a n-value|,delta,?_,hevalue,hdist⟩
    rw [M.sub_numbers,← Complex.ofReal_sub,absValue_number]
end Litex
open Filter
open scoped Topology
namespace Litex
theorem sequenceTail_index {M : Semantics.{u}} [F : FunctionSemantics M]
    (cutoff : Obj (M := M) M.Value) (hcut : In cutoff NPos)
    (index : M.Value) (hindex : M.mem index (sequenceTailValue (denote cutoff))) :
    ∃ n : ℕ, 0<n ∧ index=M.number (n : ℂ) ∧
      NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) ≤ n := by
  obtain ⟨hnpos,_,r,s,hr,hs,hrs⟩ := (F.sep_members _ _ _).mp hindex
  let obj := semanticObject index (M.member_isSet hnpos)
  obtain ⟨n,hn⟩ := (M.natural_members index).mp (inNPos_natural obj hnpos)
  let cut := NativeBridge.asNat cutoff (inNPos_natural cutoff hcut)
  have hcutval : denote cutoff=M.number (cut : ℂ) :=
    NativeBridge.asNat_spec cutoff (inNPos_natural cutoff hcut)
  have hrval : (cut : ℝ)=r :=
    Complex.ofReal_injective (M.number_injective
      (by simpa only [Complex.ofReal_natCast] using hcutval.symm.trans hr))
  have hsval : (n : ℝ)=s :=
    Complex.ofReal_injective (M.number_injective
      (by simpa only [Complex.ofReal_natCast] using hn.symm.trans hs))
  have hpositive : 0<(n : ℝ) :=
    (NativeBridge.lt_iff_ofDenoteReal (number (M := M) 0) obj 0 (n : ℝ) rfl
      (by change index=M.number ((n : ℝ) : ℂ); simpa only [Complex.ofReal_natCast] using hn)).mp (inNPos_positive obj hnpos)
  refine ⟨n,?_,hn,?_⟩
  · exact_mod_cast hpositive
  · exact_mod_cast (hrval ▸ hsval ▸ hrs)

theorem sequenceTail_member_of_le {M : Semantics.{u}} [F : FunctionSemantics M]
    (cutoff : Obj (M := M) M.Value) (hcut : In cutoff NPos)
    (n : ℕ) (hn : 0<n)
    (hle : NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) ≤ n) :
    M.mem (M.number (n : ℂ)) (sequenceTailValue (denote cutoff)) := by
  have hnmem := numberInNPosOfEq (M := M) (n : ℂ) n rfl hn
  have hcutval : denote cutoff=M.number ((NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) : ℕ) : ℂ) :=
    NativeBridge.asNat_spec cutoff (inNPos_natural cutoff hcut)
  apply (F.sep_members _ _ _).mpr
  refine ⟨hnmem,hnmem,(NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) : ℝ),(n : ℝ),?_,?_,?_⟩
  · simpa only [Complex.ofReal_natCast] using hcutval
  · simp only [Complex.ofReal_natCast]
  · exact_mod_cast hle
end Litex
namespace Litex
theorem sequenceCauchy_iff_native {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M))))) :
    SequenceCauchyValue M a ↔ CauchySeq (observeRealSequence a) := by
  constructor
  · intro h
    apply Metric.cauchySeq_iff.mpr
    intro epsilon hepsilon
    obtain ⟨cutoff,hcut,htail⟩ := h (M.number (epsilon : ℂ)) (numberInRPos epsilon hepsilon)
    let cut := NativeBridge.asNat cutoff (inNPos_natural cutoff hcut)
    refine ⟨cut+1,?_⟩
    intro m hm n hn
    have hmpos : 0<m := by omega
    have hnpos : 0<n := by omega
    have hmcut : cut≤m := by omega
    have hncut : cut≤n := by omega
    let x := M.number (m : ℂ)
    let y := M.number (n : ℂ)
    have hpair : M.mem (FiniteFunction.pack2 x y)
        (FiniteFunction.cartValue ![sequenceTailValue (denote cutoff),sequenceTailValue (denote cutoff)]) :=
      (FiniteFunction.cart2_members _ _ _).mpr
        ⟨x,sequenceTail_member_of_le cutoff hcut m hmpos hmcut,
         y,sequenceTail_member_of_le cutoff hcut n hnpos hncut,rfl⟩
    obtain ⟨_,_,r,s,hd,he,hdist⟩ := (F.sep_members _ _ _).mp (htail _ hpair)
    have hx : F.callValue (FiniteFunction.pack2 x y) (M.number 1)=x :=
      congrArg Prod.fst (FiniteFunction.unpack_pack2 x y)
    have hy : F.callValue (FiniteFunction.pack2 x y) (M.number 2)=y :=
      congrArg Prod.snd (FiniteFunction.unpack_pack2 x y)
    dsimp [x,y] at hx hy
    rw [hx,hy,observeRealSequence_spec a m hmpos hf,
      observeRealSequence_spec a n hnpos hf,M.sub_numbers,
      ← Complex.ofReal_sub,absValue_number] at hd
    have hr : r=|observeRealSequence a m-observeRealSequence a n| :=
      (Complex.ofReal_injective (M.number_injective hd)).symm
    have hs : s=epsilon := (Complex.ofReal_injective (M.number_injective he)).symm
    simpa only [Real.dist_eq,hr,hs] using hdist
  · intro h epsilon hepsilon
    let e : Obj (M := M) M.Value := semanticObject epsilon (M.member_isSet hepsilon)
    have heR : In e R := inRPos_real e hepsilon
    let delta := NativeBridge.asReal e heR
    have hevalue : epsilon=M.number (delta : ℂ) := NativeBridge.asReal_spec e heR
    have hd : 0<delta :=
      (NativeBridge.lt_iff_ofDenoteReal (number (M := M) 0) e 0 delta rfl hevalue).mp
        (inRPos_positive e hepsilon)
    obtain ⟨N,hN⟩ := (Metric.cauchySeq_iff.mp h) delta hd
    let cut := N+1
    have hcut : 0<cut := by dsimp [cut];omega
    have hcutmem := numberInNPosOfEq (M := M) (cut : ℂ) cut rfl hcut
    let cutoff : Obj (M := M) M.Value :=
      semanticObject (M.number (cut : ℂ)) (M.member_isSet hcutmem)
    have hcutnat : NativeBridge.asNat cutoff (inNPos_natural cutoff hcutmem)=cut := by
      have hv : denote cutoff=M.number ((NativeBridge.asNat cutoff (inNPos_natural cutoff hcutmem) : ℕ) : ℂ) :=
        NativeBridge.asNat_spec cutoff (inNPos_natural cutoff hcutmem)
      change M.number (cut : ℂ)=M.number ((NativeBridge.asNat cutoff (inNPos_natural cutoff hcutmem) : ℕ) : ℂ) at hv
      exact_mod_cast (M.number_injective hv).symm
    refine ⟨cutoff,hcutmem,?_⟩
    intro p hp
    obtain ⟨x,hx,y,hy,rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp hp
    obtain ⟨m,hmpos,rfl,hm⟩ := sequenceTail_index cutoff hcutmem x hx
    obtain ⟨n,hnpos,rfl,hn⟩ := sequenceTail_index cutoff hcutmem y hy
    rw [hcutnat] at hm hn
    have hmN : N≤m := by dsimp [cut] at hm;omega
    have hnN : N≤n := by dsimp [cut] at hn;omega
    have hdist : |observeRealSequence a m-observeRealSequence a n|<delta := by
      simpa only [Real.dist_eq] using hN m hmN n hnN
    have hpair : M.mem (FiniteFunction.pack2 (M.number (m : ℂ)) (M.number (n : ℂ)))
        (FiniteFunction.cartValue ![denote (NPos (M := M)),denote (NPos (M := M))]) :=
      (FiniteFunction.cart2_members _ _ _).mpr
        ⟨_,numberInNPosOfEq (m : ℂ) m rfl hmpos,
         _,numberInNPosOfEq (n : ℂ) n rfl hnpos,rfl⟩
    apply (F.sep_members _ _ _).mpr
    refine ⟨hpair,hpair,|observeRealSequence a m-observeRealSequence a n|,delta,?_,hevalue,hdist⟩
    have hxval : F.callValue (FiniteFunction.pack2 (M.number (m : ℂ)) (M.number (n : ℂ))) (M.number 1)=M.number (m : ℂ) :=
      congrArg Prod.fst (FiniteFunction.unpack_pack2 _ _)
    have hyval : F.callValue (FiniteFunction.pack2 (M.number (m : ℂ)) (M.number (n : ℂ))) (M.number 2)=M.number (n : ℂ) :=
      congrArg Prod.snd (FiniteFunction.unpack_pack2 _ _)
    rw [hxval,hyval,observeRealSequence_spec a m hmpos hf,
      observeRealSequence_spec a n hnpos hf,M.sub_numbers,
      ← Complex.ofReal_sub,absValue_number]
end Litex
namespace Litex
theorem sequenceCauchyOfCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β)
    (hf : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In value R) (h : HasSequenceLimit a value) : SequenceCauchy a := by
  let r := NativeBridge.asReal value hv
  have hr := NativeBridge.asReal_spec value hv
  change HasSequenceLimitValue M (denote a) (denote value) at h
  have ht := (sequenceLimit_iff_tendsto (denote a) r hf).mp (hr ▸ h)
  exact (sequenceCauchy_iff_native (denote a) hf).mpr ht.cauchySeq

theorem sequenceConstantProperties {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β)
    (hf : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In value R)
    (h : ∀ n, M.mem n (denote (NPos (M := M))) → F.callValue (denote a) n=denote value) :
    SequenceNondecreasing a ∧ SequenceNonincreasing a ∧
      SequenceBounded a ∧ SequenceCauchy a ∧ SequenceConvergent a := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp hv
  have hb := sequenceBoundedFromPointwise a value value hf hv hv
    (fun n hn => ⟨⟨r,r,hr,(h n hn).trans hr,le_rfl⟩,
      ⟨r,r,(h n hn).trans hr,hr,le_rfl⟩⟩)
  have ht : Tendsto (observeRealSequence (denote a)) atTop (𝓝 r) := by
    apply Metric.tendsto_atTop.mpr
    intro epsilon hepsilon
    refine ⟨1,?_⟩
    intro n hn
    have hnpos : 0<n := by omega
    have hobs : observeRealSequence (denote a) n=r := by
      unfold observeRealSequence
      have hcall : F.callValue (denote a) (M.number (n : ℂ))=denote value :=
        h _ (numberInNPosOfEq (n : ℂ) n rfl hnpos)
      rw [hcall,hr,observeRealValue_number]
    simpa only [hobs,dist_self] using hepsilon
  have hlimit : HasSequenceLimit a value := by
    change HasSequenceLimitValue M (denote a) (denote value)
    rw [hr]
    exact (sequenceLimit_iff_tendsto (denote a) r hf).mpr ht
  refine ⟨?_,?_,hb,(sequenceCauchy_iff_native (denote a) hf).mpr ht.cauchySeq,
    sequenceConvergentOfCandidate a value hv hlimit⟩
  · intro m hm n hn _
    exact ⟨r,r,(h m hm).trans hr,(h n hn).trans hr,le_rfl⟩
  · intro m hm n hn _
    exact ⟨r,r,(h n hn).trans hr,(h m hm).trans hr,le_rfl⟩
end Litex

open Filter
open scoped Topology
namespace Litex.NativeBridge
noncomputable def ofRealSequence {M : Semantics.{u}} [FunctionSemantics M]
    (f : ℕ → ℝ) : Obj (M := M) (FormulaFn M) :=
  formulaFnOn (seqSignature (R (M := M)))
    (fun x => M.number ((f (naturalValue x) : ℝ) : ℂ))
    (fun x _ => (M.real_members _).mpr ⟨f (naturalValue x),rfl⟩)

theorem ofRealSequence_mem {M : Semantics.{u}} [FunctionSemantics M]
    (f : ℕ → ℝ) : In (ofRealSequence (M := M) f) (seqSet R (isSet R)) :=
  formulaFnInFnSet _

theorem ofRealSequence_domain {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : ℕ → ℝ) : M.mem (denote (ofRealSequence (M := M) f))
      (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))) :=
  unguardedFunctionDomain (ofRealSequence f) _ _ (isSet NPos) (isSet R)
    (formulaFnInFnSet _)

theorem ofRealSequence_call {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : ℕ → ℝ) (n : ℕ) (hn : 0<n) :
    F.callValue (denote (ofRealSequence (M := M) f)) (M.number (n : ℂ)) =
      M.number ((f n : ℝ) : ℂ) := by
  let a := ofRealSequence (M := M) f
  have hnmem := numberInNPosOfEq (M := M) (n : ℂ) n rfl hn
  have hd : M.mem (M.number (n : ℂ)) a.val.signature.domain :=
    (FunctionSignature.withGuard_domain (denote (NPos (M := M))) (denote (R (M := M)))
      (isSet NPos) (isSet R) (fun _ => True) (M.number (n : ℂ))).mpr ⟨hnmem,True.intro⟩
  have h := F.call_graphValue a.val.signature.domain a.val.signature.target
    a.val.bodyValue a.wd (M.number (n : ℂ)) hd
  change F.callValue (denote a) (M.number (n : ℂ)) =
    M.number ((f (naturalValue (M.number (n : ℂ))) : ℝ) : ℂ) at h
  simpa only [naturalValue_number] using h

theorem observeRealSequence_ofRealSequence_eventually {M : Semantics.{u}}
    [F : FunctionSemantics M] (f : ℕ → ℝ) :
    observeRealSequence (denote (ofRealSequence (M := M) f)) =ᶠ[atTop] f := by
  apply eventually_atTop.mpr
  refine ⟨1,?_⟩
  intro n hn
  unfold observeRealSequence
  rw [ofRealSequence_call f n (by omega),observeRealValue_number]

theorem ofRealSequence_limit_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : ℕ → ℝ) (value : ℝ) :
    HasSequenceLimit (ofRealSequence (M := M) f) (number (value : ℂ)) ↔
      Tendsto f atTop (𝓝 value) := by
  have hevent := observeRealSequence_ofRealSequence_eventually (M := M) f
  have hiff := sequenceLimit_iff_tendsto (denote (ofRealSequence (M := M) f))
    value (ofRealSequence_domain f)
  exact ⟨fun h => (hiff.mp h).congr' hevent,fun h => hiff.mpr (h.congr' hevent.symm)⟩

theorem ofRealSequence_cauchy_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : ℕ → ℝ) : SequenceCauchy (ofRealSequence (M := M) f) ↔ CauchySeq f := by
  have hevent := observeRealSequence_ofRealSequence_eventually (M := M) f
  rw [SequenceCauchy,sequenceCauchy_iff_native _ (ofRealSequence_domain f)]
  unfold CauchySeq
  rw [Filter.map_congr hevent]
end Litex.NativeBridge

namespace Litex
noncomputable def continuityNeighborhoodValue {M : Semantics.{u}} [S : SetSemantics M]
    (side : FiniteLimitSide) (domain point radius : M.Value) : M.Value :=
  S.sepValue domain (fun input => ∃ _ : M.mem input domain,
    match side with
    | .both => RealLtValue M (finiteLimitDistanceValue .both point input) radius
    | .left => ∃ _ : RealLeValue M input point,
        RealLtValue M (finiteLimitDistanceValue .left point input) radius
    | .right => ∃ _ : RealLeValue M point input,
        RealLtValue M (finiteLimitDistanceValue .right point input) radius)

def FunctionContinuityEpsilonClauseValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f domain point epsilon : M.Value) : Prop :=
  ∃ delta : Obj (M := M) M.Value, ∃ _ : In delta RPos,
    ∀ input, M.mem input (continuityNeighborhoodValue side domain point (denote delta)) →
      M.mem input (F.preimageValue f
        (fun output => M.mem output (sequenceEpsilonBallValue (F.callValue f point) epsilon)))

def FunctionContinuousAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f point : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    FunctionContinuityEpsilonClauseValue M side f (F.domainValue f) point epsilon

def FunctionContinuousAt {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β) : Prop :=
  FunctionContinuousAtValue M side (denote f) (denote point)

theorem functionContinuousAtOfForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (domain : Obj (M := M) γ) (hd : denote domain=F.domainValue (denote f))
    (h : ∀ {δ : Type y} [Representation M δ], (epsilon : Obj (M := M) δ) →
      In epsilon RPos → FunctionContinuityEpsilonClauseValue M side
        (denote f) (denote domain) (denote point) (denote epsilon)) :
    FunctionContinuousAt side f point := by
  have hraw := forallMembersOfRepresentations RPos h
  change FunctionContinuousAtValue M side (denote f) (denote point)
  intro epsilon hepsilon
  exact hd ▸ hraw epsilon hepsilon

theorem functionContinuousAtControl {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (side : FiniteLimitSide) (f : Obj (M := M) α) (point : Obj (M := M) β)
    (epsilon : Obj (M := M) γ) (he : In epsilon RPos)
    (h : FunctionContinuousAt side f point) :
    FunctionContinuityEpsilonClauseValue M side (denote f) (F.domainValue (denote f))
      (denote point) (denote epsilon) := h (denote epsilon) he
end Litex

open Filter
open scoped Topology
namespace Litex

def continuitySide (side : FiniteLimitSide) (point input : ℝ) : Prop :=
  match side with
  | .both => True
  | .left => input ≤ point
  | .right => point ≤ input

theorem continuityDistance_eq_abs (side : FiniteLimitSide) (point input : ℝ)
    (h : continuitySide side point input) : finiteLimitDistance side point input=|input-point| := by
  cases side with
  | both => rfl
  | left =>
    change input ≤ point at h
    simp only [finiteLimitDistance, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
  | right =>
    change point ≤ input at h
    simp only [finiteLimitDistance, abs_of_nonneg (sub_nonneg.mpr h)]

theorem continuityNeighborhood_numbers_iff {M : Semantics.{u}} [SetSemantics M]
    (side : FiniteLimitSide) (domain : M.Value) (point radius input : ℝ) :
    M.mem (M.number (input : ℂ)) (continuityNeighborhoodValue side domain
      (M.number (point : ℂ)) (M.number (radius : ℂ))) ↔
      M.mem (M.number (input : ℂ)) domain ∧ continuitySide side point input ∧
        finiteLimitDistance side point input < radius := by
  cases side <;> simp only [continuityNeighborhoodValue, SetSemantics.sep_members,
    finiteLimitDistanceValue_numbers, realLtValue_numbers, realLeValue_numbers,
    continuitySide, exists_prop, and_self_left, true_and]

def continuityApproachSet (M : Semantics.{u}) [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (point : ℝ) : Set ℝ :=
  {x | M.mem (M.number (x : ℂ)) (F.domainValue f) ∧ continuitySide side point x}

def FunctionContinuityEpsilonRealValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (point : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
    ∀ input : ℝ, M.mem (M.number (input : ℂ)) (F.domainValue f) →
      continuitySide side point input → finiteLimitDistance side point input < delta →
      |observeRealFunction f input - observeRealFunction f point| < epsilon

theorem functionContinuity_iff_epsilonReal {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (hf : RealFunctionValue M f)
    (point : ℝ) (hp : M.mem (M.number (point : ℂ)) (F.domainValue f)) :
    FunctionContinuousAtValue M side f (M.number (point : ℂ)) ↔
      FunctionContinuityEpsilonRealValue M side f point := by
  have hfc := hf
  obtain ⟨signature,hfn,hreal,_⟩ := hfc
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  constructor
  · intro h epsilon hepsilon
    obtain ⟨delta,hdelta,hcontrol⟩ := h (M.number (epsilon : ℂ)) (numberInRPos epsilon hepsilon)
    obtain ⟨d,hd,hpositive⟩ := NativeBridge.realWitnessOfPositive delta (inRPos_positive delta hdelta)
    refine ⟨d,hpositive,?_⟩
    intro x hx hside hnear
    have hn : M.mem (M.number (x : ℂ)) (continuityNeighborhoodValue side (F.domainValue f)
        (M.number (point : ℂ)) (denote delta)) := by
      rw [hd]
      exact (continuityNeighborhood_numbers_iff side _ point d x).mpr ⟨hx,hside,hnear⟩
    have image := ((F.preimage_mem_iff _ signature.domain_isSet hfn).mp (hcontrol _ hn)).2
    rw [observeRealFunction_spec f hf point hp,observeRealFunction_spec f hf x hx] at image
    exact (sequenceEpsilonBall_numbers _ epsilon _).mp image
  · intro h epsilon hepsilon
    let e : Obj (M := M) M.Value := semanticObject epsilon (M.member_isSet hepsilon)
    have he : In e RPos := hepsilon
    obtain ⟨eps,hevalue,hepositive⟩ := NativeBridge.realWitnessOfPositive e (inRPos_positive e he)
    change epsilon = M.number (eps : ℂ) at hevalue
    obtain ⟨delta,hdelta,hcontrol⟩ := h eps hepositive
    let d : Obj (M := M) M.Value := semanticObject (M.number (delta : ℂ))
      (M.member_isSet (numberInRPos delta hdelta))
    refine ⟨d,numberInRPos delta hdelta,?_⟩
    intro input hnear
    have hxgraph : M.mem input (F.domainValue f) := ((F.sep_members _ _ _).mp hnear).1
    obtain ⟨x,hx⟩ := (M.real_members input).mp (hreal input (hdomain ▸ hxgraph))
    change M.mem input (continuityNeighborhoodValue side (F.domainValue f)
      (M.number (point : ℂ)) (M.number (delta : ℂ))) at hnear
    rw [hx] at hnear
    have hn := (continuityNeighborhood_numbers_iff side _ point delta x).mp hnear
    apply (F.preimage_mem_iff _ signature.domain_isSet hfn).mpr
    refine ⟨hdomain ▸ hxgraph,?_⟩
    rw [hx,observeRealFunction_spec f hf point hp,observeRealFunction_spec f hf x hn.1,hevalue]
    exact (sequenceEpsilonBall_numbers _ eps _).mpr (hcontrol x hn.1 hn.2.1 hn.2.2)

theorem functionContinuity_iff_native {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f : M.Value) (hf : RealFunctionValue M f)
    (point : ℝ) (hp : M.mem (M.number (point : ℂ)) (F.domainValue f)) :
    FunctionContinuousAtValue M side f (M.number (point : ℂ)) ↔
      ContinuousWithinAt (observeRealFunction f) (continuityApproachSet M side f point) point := by
  rw [functionContinuity_iff_epsilonReal side f hf point hp,ContinuousWithinAt,
    Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h epsilon hepsilon
    obtain ⟨delta,hdelta,hcontrol⟩ := h epsilon hepsilon
    refine ⟨delta,hdelta,?_⟩
    intro x hx hnear
    have hd := continuityDistance_eq_abs side point x hx.2
    simpa only [Real.dist_eq] using hcontrol x hx.1 hx.2
      (by simpa only [hd,Real.dist_eq] using hnear)
  · intro h epsilon hepsilon
    obtain ⟨delta,hdelta,hcontrol⟩ := h epsilon hepsilon
    refine ⟨delta,hdelta,?_⟩
    intro x hx hside hnear
    have hd := continuityDistance_eq_abs side point x hside
    have hclose := hcontrol (x := x) ⟨hx,hside⟩
      (by simpa only [Real.dist_eq,← hd] using hnear)
    simpa only [Real.dist_eq] using hclose
theorem functionContinuousAtOfConstant {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f point value : M.Value) (hf : RealFunctionValue M f)
    (hp : M.mem point (F.domainValue f)) (hv : M.mem value (denote (R (M := M))))
    (h : ∀ x, M.mem x (F.domainValue f) → F.callValue f x=value) :
    FunctionContinuousAtValue M side f point := by
  have hfc := hf
  obtain ⟨signature,hfn,hreal,_⟩ := hfc
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpvalue⟩ := (M.real_members point).mp (hreal point (hdomain ▸ hp))
  obtain ⟨r,hr⟩ := (M.real_members value).mp hv
  rw [hpvalue]
  have hpnum : M.mem (M.number (p : ℂ)) (F.domainValue f) := hpvalue ▸ hp
  apply (functionContinuity_iff_epsilonReal side f hf p hpnum).mpr
  intro epsilon hepsilon
  refine ⟨1,zero_lt_one,?_⟩
  intro x hx _ _
  have hxvalue : observeRealFunction f x=r := by
    unfold observeRealFunction
    rw [h _ hx,hr,observeRealValue_number]
  have hpobserve : observeRealFunction f p=r := by
    unfold observeRealFunction
    rw [h _ hpnum,hr,observeRealValue_number]
  simpa only [hxvalue,hpobserve,sub_self,abs_zero] using hepsilon

theorem functionContinuousAtOfIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f point : M.Value) (hf : RealFunctionValue M f)
    (hp : M.mem point (F.domainValue f))
    (h : ∀ x, M.mem x (F.domainValue f) → F.callValue f x=x) :
    FunctionContinuousAtValue M side f point := by
  have hfc := hf
  obtain ⟨signature,hfn,hreal,_⟩ := hfc
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpvalue⟩ := (M.real_members point).mp (hreal point (hdomain ▸ hp))
  rw [hpvalue]
  have hpnum : M.mem (M.number (p : ℂ)) (F.domainValue f) := hpvalue ▸ hp
  apply (functionContinuity_iff_epsilonReal side f hf p hpnum).mpr
  intro epsilon hepsilon
  refine ⟨epsilon,hepsilon,?_⟩
  intro x hx hside hnear
  have hxvalue : observeRealFunction f x=x := by
    unfold observeRealFunction
    rw [h _ hx,observeRealValue_number]
  have hpobserve : observeRealFunction f p=p := by
    unfold observeRealFunction
    rw [h _ hpnum,observeRealValue_number]
  rw [continuityDistance_eq_abs side p x hside] at hnear
  simpa only [hxvalue,hpobserve] using hnear
end Litex

open Filter
open scoped Topology
namespace Litex.NativeBridge
noncomputable def ofRealFunction {M : Semantics.{u}} [FunctionSemantics M]
    (f : ℝ → ℝ) : Obj (M := M) (FormulaFn M) :=
  formulaFnOn (FunctionSignature.one .real .real (fun _ => True))
    (fun x => M.number ((f (observeRealValue x) : ℝ) : ℂ))
    (fun x _ => (M.real_members _).mpr ⟨f (observeRealValue x),rfl⟩)

theorem ofRealFunction_mem {M : Semantics.{u}} [FunctionSemantics M]
    (f : ℝ → ℝ) : In (ofRealFunction (M := M) f)
      (fnSet (FunctionSignature.one .real .real (fun _ => True))) := formulaFnInFnSet _

theorem ofRealFunction_domain {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : ℝ → ℝ) : F.domainValue (denote (ofRealFunction (M := M) f))=denote R := by
  have hmem := unguardedFunctionDomain (ofRealFunction (M := M) f) (denote R) (denote R)
    (isSet R) (isSet R) (ofRealFunction_mem f)
  exact F.domainValue_eq (isSet R) hmem

theorem ofRealFunction_real {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : ℝ → ℝ) : RealFunctionValue M (denote (ofRealFunction (M := M) f)) := by
  refine ⟨_,ofRealFunction_mem f,?_,fun _ hx => hx⟩
  intro x hx
  exact ((F.sep_members _ _ _).mp hx).1

theorem ofRealFunction_call {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : ℝ → ℝ) (x : ℝ) :
    F.callValue (denote (ofRealFunction (M := M) f)) (M.number (x : ℂ)) = M.number (f x : ℂ) := by
  let a := ofRealFunction (M := M) f
  have hx : M.mem (M.number (x : ℂ)) a.val.signature.domain :=
    (FunctionSignature.withGuard_domain _ _ (isSet R) (isSet R) (fun _ => True) _).mpr
      ⟨numberInR x,True.intro⟩
  have h := F.call_graphValue a.val.signature.domain a.val.signature.target a.val.bodyValue a.wd
    (M.number (x : ℂ)) hx
  change F.callValue (denote a) (M.number (x : ℂ))=
    M.number (f (observeRealValue (M.number (x : ℂ))) : ℂ) at h
  simpa only [observeRealValue_number] using h

theorem observeRealFunction_ofRealFunction {M : Semantics.{u}} [FunctionSemantics M]
    (f : ℝ → ℝ) : observeRealFunction (denote (ofRealFunction (M := M) f))=f := by
  funext x
  unfold observeRealFunction
  rw [ofRealFunction_call,observeRealValue_number]

theorem ofRealFunction_continuity_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : ℝ → ℝ) (point : ℝ) :
    FunctionContinuousAt .both (ofRealFunction (M := M) f) (number (point : ℂ)) ↔
      ContinuousAt f point := by
  have hp : M.mem (M.number (point : ℂ)) (F.domainValue (denote (ofRealFunction (M := M) f))) := by
    rw [ofRealFunction_domain]
    exact numberInR point
  have h := functionContinuity_iff_native .both (denote (ofRealFunction (M := M) f))
    (ofRealFunction_real f) point hp
  have hset : continuityApproachSet M .both (denote (ofRealFunction (M := M) f)) point=Set.univ := by
    ext x
    simp only [continuityApproachSet,ofRealFunction_domain,Set.mem_setOf_eq,
      continuitySide,and_true,Set.mem_univ,iff_true]
    exact numberInR x
  change FunctionContinuousAtValue M .both (denote (ofRealFunction (M := M) f)) (M.number (point : ℂ)) ↔ ContinuousAt f point
  simpa only [hset,observeRealFunction_ofRealFunction,
    continuousWithinAt_univ] using h
end Litex.NativeBridge

open Filter
open scoped Topology
namespace Litex

def RealAccumulationValue (M : Semantics.{u}) [SetSemantics M]
    (side : FiniteLimitSide) (domain point : M.Value) : Prop :=
  ∀ radius, M.mem radius (denote (RPos (M := M))) →
    FiniteLimitAccumulationClauseValue M side domain point radius

def RealAccumulation {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (side : FiniteLimitSide) (domain : Obj (M := M) α) (point : Obj (M := M) β) : Prop :=
  RealAccumulationValue M side (denote domain) (denote point)

theorem realAccumulationOfForall {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (side : FiniteLimitSide) (domain : Obj (M := M) α) (point : Obj (M := M) β)
    (h : ∀ {γ : Type x} [Representation M γ], (radius : Obj (M := M) γ) →
      In radius RPos → FiniteLimitAccumulationClauseValue M side (denote domain)
        (denote point) (denote radius)) : RealAccumulation side domain point :=
  forallMembersOfRepresentations RPos h

theorem functionContinuousAtOfLimit {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f point : M.Value) (hf : RealFunctionValue M f)
    (hp : M.mem point (F.domainValue f))
    (h : HasFiniteFunctionLimitValue M side f point (F.callValue f point)) :
    FunctionContinuousAtValue M side f point := by
  obtain ⟨p,l,hpoint,hvalue,_,hcontrol⟩ := h
  have hpnum : M.mem (M.number (p : ℂ)) (F.domainValue f) := hpoint ▸ hp
  have hobservation : l=observeRealFunction f p :=
    Complex.ofReal_injective (M.number_injective
      (hvalue.symm.trans (by rw [hpoint];exact observeRealFunction_spec f hf p hpnum)))
  rw [hpoint]
  apply (functionContinuity_iff_epsilonReal side f hf p hpnum).mpr
  intro epsilon hepsilon
  obtain ⟨delta,hdelta,hnear⟩ := hcontrol epsilon hepsilon
  refine ⟨delta,hdelta,?_⟩
  intro x hx hside hclose
  by_cases heq : x=p
  · subst x
    simpa only [sub_self,abs_zero] using hepsilon
  · have hpositive : 0<finiteLimitDistance side p x := by
      rw [continuityDistance_eq_abs side p x hside]
      exact abs_pos.mpr (sub_ne_zero.mpr heq)
    obtain ⟨y,hy,hyclose⟩ := hnear x hx hpositive hclose
    have hyobs : y=observeRealFunction f x :=
      Complex.ofReal_injective (M.number_injective
        (hy.symm.trans (observeRealFunction_spec f hf x hx)))
    simpa only [hyobs,hobservation] using hyclose

theorem functionLimitOfContinuousAt {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f point : M.Value) (hf : RealFunctionValue M f)
    (hp : M.mem point (F.domainValue f)) (hc : FunctionContinuousAtValue M side f point)
    (ha : RealAccumulationValue M side (F.domainValue f) point) :
    HasFiniteFunctionLimitValue M side f point (F.callValue f point) := by
  have hfc := hf
  obtain ⟨signature,hfn,hreal,_⟩ := hfc
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpoint⟩ := (M.real_members point).mp (hreal point (hdomain ▸ hp))
  have hpnum : M.mem (M.number (p : ℂ)) (F.domainValue f) := hpoint ▸ hp
  have hc := (functionContinuity_iff_epsilonReal side f hf p hpnum).mp (hpoint ▸ hc)
  refine ⟨p,observeRealFunction f p,hpoint,?_,?_,?_⟩
  · rw [hpoint]
    exact observeRealFunction_spec f hf p hpnum
  · intro radius hradius
    obtain ⟨x,hx,hpositive,hnear⟩ := ha (M.number (radius : ℂ)) (numberInRPos radius hradius)
    obtain ⟨r,hr⟩ := (M.real_members (denote x)).mp (hreal _ (hdomain ▸ hx))
    refine ⟨r,hr ▸ hx,?_,?_⟩
    · rw [hpoint,hr,finiteLimitDistanceValue_numbers] at hpositive
      exact (realLtValue_numbers 0 _).mp hpositive
    · rw [hpoint,hr,finiteLimitDistanceValue_numbers] at hnear
      exact (realLtValue_numbers _ radius).mp hnear
  · intro epsilon hepsilon
    obtain ⟨delta,hdelta,hcontrol⟩ := hc epsilon hepsilon
    refine ⟨delta,hdelta,?_⟩
    intro x hx hpositive hclose
    have hside : continuitySide side p x := by
      cases side with
      | both => trivial
      | left => change 0<p-x at hpositive; change x≤p;linarith
      | right => change 0<x-p at hpositive; change p≤x;linarith
    exact ⟨observeRealFunction f x,observeRealFunction_spec f hf x hx,
      hcontrol x hx hside hclose⟩
end Litex

open Filter
open scoped Topology
namespace Litex

theorem continuitySide_self (side : FiniteLimitSide) (point : ℝ) : continuitySide side point point := by
  cases side with
  | both => trivial
  | left => exact le_rfl
  | right => exact le_rfl

theorem functionContinuousAtMap {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f out point : M.Value)
    (hf : RealFunctionValue M f) (hout : RealFunctionValue M out)
    (hD : ∀ x, M.mem x (F.domainValue out) → M.mem x (F.domainValue f))
    (hp : M.mem point (F.domainValue out))
    (rawOp : M.Value → M.Value) (nativeOp : ℝ → ℝ)
    (hop : ∀ x : ℝ, rawOp (M.number (x : ℂ)) = M.number (nativeOp x : ℂ))
    (hformula : ∀ x, M.mem x (F.domainValue out) → F.callValue out x=rawOp (F.callValue f x))
    (hcontinuous : Continuous nativeOp) (hc : FunctionContinuousAtValue M side f point) :
    FunctionContinuousAtValue M side out point := by
  have houtcopy := hout
  obtain ⟨signature,hfn,hreal,_⟩ := houtcopy
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpoint⟩ := (M.real_members point).mp (hreal point (hdomain ▸ hp))
  have hpout : M.mem (M.number (p : ℂ)) (F.domainValue out) := hpoint ▸ hp
  have hpf := hD _ hpout
  have hsource := (functionContinuity_iff_native side f hf p hpf).mp (hpoint ▸ hc)
  have hrestriction : continuityApproachSet M side out p ⊆ continuityApproachSet M side f p :=
    fun _ hx => ⟨hD _ hx.1,hx.2⟩
  have mapped := hcontinuous.continuousAt.comp_continuousWithinAt (hsource.mono hrestriction)
  have heq : ∀ x ∈ continuityApproachSet M side out p,
      observeRealFunction out x=nativeOp (observeRealFunction f x) := by
    intro x hx
    have equation := hformula (M.number (x : ℂ)) hx.1
    rw [observeRealFunction_spec f hf x (hD _ hx.1),hop] at equation
    unfold observeRealFunction
    rw [equation,observeRealValue_number]
    rfl
  rw [hpoint]
  exact (functionContinuity_iff_native side out hout p hpout).mpr
    (mapped.congr_of_mem heq ⟨hpout,continuitySide_self side p⟩)

theorem functionContinuousAtMapTwo {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f g out point : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g) (hout : RealFunctionValue M out)
    (hDf : ∀ x, M.mem x (F.domainValue out) → M.mem x (F.domainValue f))
    (hDg : ∀ x, M.mem x (F.domainValue out) → M.mem x (F.domainValue g))
    (hp : M.mem point (F.domainValue out))
    (rawOp : M.Value → M.Value → M.Value) (nativeOp : ℝ → ℝ → ℝ)
    (hop : ∀ x y : ℝ, rawOp (M.number (x : ℂ)) (M.number (y : ℂ))=M.number (nativeOp x y : ℂ))
    (hformula : ∀ x, M.mem x (F.domainValue out) →
      F.callValue out x=rawOp (F.callValue f x) (F.callValue g x))
    (hcontinuous : Continuous (fun pair : ℝ × ℝ => nativeOp pair.1 pair.2))
    (hcf : FunctionContinuousAtValue M side f point) (hcg : FunctionContinuousAtValue M side g point) :
    FunctionContinuousAtValue M side out point := by
  have houtcopy := hout
  obtain ⟨signature,hfn,hreal,_⟩ := houtcopy
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpoint⟩ := (M.real_members point).mp (hreal point (hdomain ▸ hp))
  have hpout : M.mem (M.number (p : ℂ)) (F.domainValue out) := hpoint ▸ hp
  have source := (functionContinuity_iff_native side f hf p (hDf _ hpout)).mp (hpoint ▸ hcf)
  have other := (functionContinuity_iff_native side g hg p (hDg _ hpout)).mp (hpoint ▸ hcg)
  have first := source.mono (show continuityApproachSet M side out p ⊆ continuityApproachSet M side f p from fun _ hx => ⟨hDf _ hx.1,hx.2⟩)
  have second := other.mono (show continuityApproachSet M side out p ⊆ continuityApproachSet M side g p from fun _ hx => ⟨hDg _ hx.1,hx.2⟩)
  have mapped := hcontinuous.continuousAt.comp_continuousWithinAt (first.prodMk second)
  have heq : ∀ x ∈ continuityApproachSet M side out p,
      observeRealFunction out x=nativeOp (observeRealFunction f x) (observeRealFunction g x) := by
    intro x hx
    have equation := hformula (M.number (x : ℂ)) hx.1
    rw [observeRealFunction_spec f hf x (hDf _ hx.1),observeRealFunction_spec g hg x (hDg _ hx.1),hop] at equation
    unfold observeRealFunction
    rw [equation,observeRealValue_number]
    rfl
  rw [hpoint]
  exact (functionContinuity_iff_native side out hout p hpout).mpr
    (mapped.congr_of_mem heq ⟨hpout,continuitySide_self side p⟩)

theorem functionContinuousAtDivide {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f g out point : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g) (hout : RealFunctionValue M out)
    (hDf : ∀ x, M.mem x (F.domainValue out) → M.mem x (F.domainValue f))
    (hDg : ∀ x, M.mem x (F.domainValue out) → M.mem x (F.domainValue g))
    (hp : M.mem point (F.domainValue out))
    (hformula : ∀ x, M.mem x (F.domainValue out) →
      F.callValue out x=M.divValue (F.callValue f x) (F.callValue g x))
    (hnonzero : F.callValue g point≠M.number 0)
    (hcf : FunctionContinuousAtValue M side f point) (hcg : FunctionContinuousAtValue M side g point) :
    FunctionContinuousAtValue M side out point := by
  have houtcopy := hout
  obtain ⟨signature,hfn,hreal,_⟩ := houtcopy
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpoint⟩ := (M.real_members point).mp (hreal point (hdomain ▸ hp))
  have hpout : M.mem (M.number (p : ℂ)) (F.domainValue out) := hpoint ▸ hp
  have source := (functionContinuity_iff_native side f hf p (hDf _ hpout)).mp (hpoint ▸ hcf)
  have other := (functionContinuity_iff_native side g hg p (hDg _ hpout)).mp (hpoint ▸ hcg)
  have first := source.mono (show continuityApproachSet M side out p ⊆ continuityApproachSet M side f p from fun _ hx => ⟨hDf _ hx.1,hx.2⟩)
  have second := other.mono (show continuityApproachSet M side out p ⊆ continuityApproachSet M side g p from fun _ hx => ⟨hDg _ hx.1,hx.2⟩)
  have hden : observeRealFunction g p≠0 := by
    intro hzero
    apply hnonzero
    rw [hpoint,observeRealFunction_spec g hg p (hDg _ hpout),hzero,Complex.ofReal_zero]
  have mapped := first.div second hden
  have hnz := second.eventually (eventually_ne_nhds hden)
  have heq : observeRealFunction out =ᶠ[𝓝[continuityApproachSet M side out p] p]
      (fun x => observeRealFunction f x / observeRealFunction g x) := by
    filter_upwards [self_mem_nhdsWithin,hnz] with x hx hnonzero
    have hcomplex : (observeRealFunction g x : ℂ) ≠ 0 := by exact_mod_cast hnonzero
    have equation := hformula (M.number (x : ℂ)) hx.1
    rw [observeRealFunction_spec f hf x (hDf _ hx.1),observeRealFunction_spec g hg x (hDg _ hx.1),
      M.div_numbers _ _ hcomplex,← Complex.ofReal_div] at equation
    unfold observeRealFunction
    rw [equation,observeRealValue_number]
    rfl
  rw [hpoint]
  exact (functionContinuity_iff_native side out hout p hpout).mpr
    (mapped.congr_of_eventuallyEq_of_mem heq ⟨hpout,continuitySide_self side p⟩)
end Litex

open Filter
open scoped Topology
namespace Litex

theorem functionContinuousAtCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    (side : FiniteLimitSide) (f g out point : M.Value)
    (hf : RealFunctionValue M f) (hg : RealFunctionValue M g) (hout : RealFunctionValue M out)
    (hDf : ∀ x, M.mem x (F.domainValue out) → M.mem x (F.domainValue f))
    (hp : M.mem point (F.domainValue out))
    (hmaps : ∀ x, M.mem x (F.domainValue out) → M.mem (F.callValue f x) (F.domainValue g))
    (hformula : ∀ x, M.mem x (F.domainValue out) → F.callValue out x=F.callValue g (F.callValue f x))
    (hcf : FunctionContinuousAtValue M side f point)
    (hcg : FunctionContinuousAtValue M .both g (F.callValue f point)) :
    FunctionContinuousAtValue M side out point := by
  have houtcopy := hout
  obtain ⟨signature,hfn,hreal,_⟩ := houtcopy
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  obtain ⟨p,hpoint⟩ := (M.real_members point).mp (hreal point (hdomain ▸ hp))
  have hpout : M.mem (M.number (p : ℂ)) (F.domainValue out) := hpoint ▸ hp
  have hvalue : F.callValue f point=M.number (observeRealFunction f p : ℂ) := by
    rw [hpoint]
    exact observeRealFunction_spec f hf p (hDf _ hpout)
  have hpg : M.mem (M.number (observeRealFunction f p : ℂ)) (F.domainValue g) := hvalue ▸ hmaps point hp
  have inner := (functionContinuity_iff_native side f hf p (hDf _ hpout)).mp (hpoint ▸ hcf)
  have outer := (functionContinuity_iff_native .both g hg (observeRealFunction f p) hpg).mp (hvalue ▸ hcg)
  have restricted := inner.mono (show continuityApproachSet M side out p ⊆ continuityApproachSet M side f p from fun _ hx => ⟨hDf _ hx.1,hx.2⟩)
  have hmapped : Set.MapsTo (observeRealFunction f) (continuityApproachSet M side out p)
      (continuityApproachSet M .both g (observeRealFunction f p)) := by
    intro x hx
    have hm := hmaps (M.number (x : ℂ)) hx.1
    rw [observeRealFunction_spec f hf x (hDf _ hx.1)] at hm
    exact ⟨hm,True.intro⟩
  have composed := outer.comp restricted hmapped
  have heq : ∀ x ∈ continuityApproachSet M side out p,
      observeRealFunction out x=observeRealFunction g (observeRealFunction f x) := by
    intro x hx
    have equation := hformula (M.number (x : ℂ)) hx.1
    rw [observeRealFunction_spec f hf x (hDf _ hx.1)] at equation
    unfold observeRealFunction
    rw [equation]
    rfl
  rw [hpoint]
  exact (functionContinuity_iff_native side out hout p hpout).mpr
    (composed.congr_of_mem heq ⟨hpout,continuitySide_self side p⟩)
end Litex

namespace Litex

def sequenceExtremumRayValue {M : Semantics.{u}} [SetSemantics M]
    (upper : Bool) (value epsilon : M.Value) : M.Value :=
  SetSemantics.sepValue (denote (R (M := M))) (fun y =>
    ∃ _ : M.mem y (denote (R (M := M))),
      if upper then RealLtValue M y (M.addValue value epsilon)
      else RealLtValue M (M.subValue value epsilon) y)

def SequenceExtremumBoundValue (M : Semantics.{u}) [FunctionSemantics M]
    (upper : Bool) (a value epsilon cutoff : M.Value) : Prop :=
  ∀ n, M.mem n (sequenceTailValue cutoff) →
    M.mem n (FunctionSemantics.preimageValue a
      (fun y => M.mem y (sequenceExtremumRayValue upper value epsilon)))

def SequenceExtremumHitValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (upper : Bool) (a value epsilon cutoff : M.Value) : Prop :=
  ∃ n : Obj (M := M) M.Value, ∃ _ : In n NPos,
    (∃ r s : ℝ, cutoff=M.number (r : ℂ) ∧ denote n=M.number (s : ℂ) ∧ r≤s) ∧
    (if upper then RealLtValue M (M.subValue value epsilon) (F.callValue a (denote n))
      else RealLtValue M (F.callValue a (denote n)) (M.addValue value epsilon))

def HasSequenceExtremumValue (M : Semantics.{u}) [FunctionSemantics M]
    (upper : Bool) (a value : M.Value) : Prop :=
  (∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
      SequenceExtremumBoundValue M upper a value epsilon (denote cutoff)) ∧
  (∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∀ cutoff, M.mem cutoff (denote (NPos (M := M))) →
      SequenceExtremumHitValue M upper a value epsilon cutoff)

def HasSequenceExtremum {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (upper : Bool) (a : Obj (M := M) α) (value : Obj (M := M) β) : Prop :=
  HasSequenceExtremumValue M upper (denote a) (denote value)

abbrev HasSequenceLimsup {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β) := HasSequenceExtremum true a value
abbrev HasSequenceLiminf {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β) := HasSequenceExtremum false a value

theorem sequenceExtremumOfForall {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (upper : Bool) (a : Obj (M := M) α) (value : Obj (M := M) β)
    (hb : ∀ {γ : Type x} [Representation M γ], (epsilon : Obj (M := M) γ) → In epsilon RPos →
      ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
        SequenceExtremumBoundValue M upper (denote a) (denote value) (denote epsilon) (denote cutoff))
    (hh : ∀ {γ : Type y} [Representation M γ], (epsilon : Obj (M := M) γ) → In epsilon RPos →
      ∀ {δ : Type z} [Representation M δ], (cutoff : Obj (M := M) δ) → In cutoff NPos →
        SequenceExtremumHitValue M upper (denote a) (denote value) (denote epsilon) (denote cutoff)) :
    HasSequenceExtremum upper a value :=
  ⟨forallMembersOfRepresentations RPos hb,
    forallMembersOfRepresentations RPos (fun epsilon hepsilon =>
      forallMembersOfRepresentations NPos (fun cutoff hcutoff => hh epsilon hepsilon cutoff hcutoff))⟩

theorem sequenceExtremumBoundAtIndex {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a : M.Value) (r epsilon : ℝ)
    (cutoff : Obj (M := M) M.Value) (hcut : In cutoff NPos)
    (n : ℕ) (hn : 0<n)
    (hle : NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) ≤ n)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : SequenceExtremumBoundValue M upper a (M.number (r : ℂ))
      (M.number (epsilon : ℂ)) (denote cutoff)) :
    if upper then observeRealSequence a n < r+epsilon else r-epsilon < observeRealSequence a n := by
  have hi := hb _ (sequenceTail_member_of_le cutoff hcut n hn hle)
  have hp := (F.preimage_mem_iff
    (fun y => M.mem y (sequenceExtremumRayValue upper (M.number (r : ℂ)) (M.number (epsilon : ℂ))))
    (isSet (NPos (M := M))) hf).mp hi
  obtain ⟨_, _, h⟩ := (F.sep_members _ _ _).mp hp.2
  rw [observeRealSequence_spec a n hn hf] at h
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, M.add_numbers, M.sub_numbers,
    ← Complex.ofReal_add, ← Complex.ofReal_sub, realLtValue_numbers] at h ⊢ <;> exact h

theorem sequenceExtremumHitAtTail {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a : M.Value) (r epsilon : ℝ)
    (cutoff : Obj (M := M) M.Value) (hcut : In cutoff NPos)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hh : SequenceExtremumHitValue M upper a (M.number (r : ℂ))
      (M.number (epsilon : ℂ)) (denote cutoff)) :
    ∃ n : ℕ, 0<n ∧ NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) ≤ n ∧
      (if upper then r-epsilon < observeRealSequence a n else observeRealSequence a n < r+epsilon) := by
  obtain ⟨index, hindex, hle, hhit⟩ := hh
  let n := NativeBridge.asNat index (inNPos_natural index hindex)
  have hnv : denote index=M.number (n : ℂ) := NativeBridge.asNat_spec index (inNPos_natural index hindex)
  have hn : 0<n := by
    have hp := (NativeBridge.lt_iff_ofDenoteReal (number (M := M) 0) index 0 (n : ℝ)
      rfl (by simpa only [Complex.ofReal_natCast] using hnv)).mp (inNPos_positive index hindex)
    exact_mod_cast hp
  refine ⟨n, hn, ?_, ?_⟩
  · obtain ⟨r,s,hr,hs,hrs⟩ := hle
    have hcv : denote cutoff=M.number ((NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) : ℕ) : ℂ) := NativeBridge.asNat_spec cutoff (inNPos_natural cutoff hcut)
    have hc : (NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) : ℝ)=r :=
      Complex.ofReal_injective (M.number_injective (by simpa only [Complex.ofReal_natCast] using hcv.symm.trans hr))
    have hi : (n : ℝ)=s :=
      Complex.ofReal_injective (M.number_injective (by simpa only [Complex.ofReal_natCast] using hnv.symm.trans hs))
    exact_mod_cast (hc ▸ hi ▸ hrs)
  · rw [hnv,observeRealSequence_spec a n hn hf] at hhit
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, M.add_numbers, M.sub_numbers,
      ← Complex.ofReal_add, ← Complex.ofReal_sub, realLtValue_numbers] at hhit ⊢ <;> exact hhit

theorem sequenceExtremumUnique {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a : M.Value) (r s : ℝ)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hr : HasSequenceExtremumValue M upper a (M.number (r : ℂ)))
    (hs : HasSequenceExtremumValue M upper a (M.number (s : ℂ))) : r=s := by
  have ordered : ∀ r s : ℝ, HasSequenceExtremumValue M upper a (M.number (r : ℂ)) →
      HasSequenceExtremumValue M upper a (M.number (s : ℂ)) →
      (if upper then s≤r else r≤s) := by
    intro r s hr hs
    cases upper
    · change r≤s
      by_contra h
      have hpos : 0<(r-s)/3 := by linarith
      obtain ⟨cut',hcut',hbound'⟩ := hr.1 _ (numberInRPos _ hpos)
      obtain ⟨m,hm,hle',hhit'⟩ := sequenceExtremumHitAtTail false a s ((r-s)/3) cut' hcut' hf
        (hs.2 _ (numberInRPos _ hpos) _ hcut')
      have hb' := sequenceExtremumBoundAtIndex false a r ((r-s)/3) cut' hcut' m hm hle' hf hbound'
      change observeRealSequence a m<s+(r-s)/3 at hhit'
      change r-(r-s)/3<observeRealSequence a m at hb'
      linarith
    · change s≤r
      by_contra h
      have hpos : 0<(s-r)/3 := by linarith
      obtain ⟨cut,hcut,hbound⟩ := hr.1 _ (numberInRPos _ hpos)
      obtain ⟨n,hn,hle,hhit⟩ := sequenceExtremumHitAtTail true a s ((s-r)/3) cut hcut hf
        (hs.2 _ (numberInRPos _ hpos) _ hcut)
      have hb := sequenceExtremumBoundAtIndex true a r ((s-r)/3) cut hcut n hn hle hf hbound
      change s-(s-r)/3<observeRealSequence a n at hhit
      change observeRealSequence a n<r+(s-r)/3 at hb
      linarith
  have h1 := ordered r s hr hs
  have h2 := ordered s r hs hr
  cases upper
  · exact le_antisymm h1 h2
  · exact le_antisymm h2 h1

def SequenceExtremumExistsValue (M : Semantics.{u}) [FunctionSemantics M]
    (upper : Bool) (a : M.Value) : Prop :=
  ∃ value : Obj (M := M) M.Value, ∃ _ : In value R,
    HasSequenceExtremumValue M upper a (denote value)

noncomputable def sequenceExtremumValue {M : Semantics.{u}} [FunctionSemantics M]
    (upper : Bool) (a : M.Value) : M.Value := by
  classical
  exact if h : SequenceExtremumExistsValue M upper a then denote (Classical.choose h) else M.number 0

structure SequenceExtremumObj {M : Semantics.{u}} (upper : Bool) (α : Type v)
    [Representation M α] where
  sequence : Obj (M := M) α

noncomputable instance sequenceExtremumRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (upper : Bool) :
    Representation M (SequenceExtremumObj (M := M) upper α) where
  wd p := M.mem (denote p.sequence) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))) ∧
    SequenceExtremumExistsValue M upper (denote p.sequence)
  denote p := sequenceExtremumValue upper (denote p.sequence)
  wd_isSet {p} hp := by
    classical
    unfold sequenceExtremumValue
    rw [dif_pos hp.2]
    exact M.member_isSet (Classical.choose_spec hp.2).1

noncomputable def sequenceExtremum {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (upper : Bool) (a : Obj (M := M) α)
    (ha : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hc : SequenceExtremumExistsValue M upper (denote a)) :
    Obj (M := M) (SequenceExtremumObj (M := M) upper α) := ⟨⟨a⟩, ha, hc⟩

theorem sequenceExtremumExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (upper : Bool) (a : Obj (M := M) α) (value : Obj (M := M) β) (hv : In value R)
    (h : HasSequenceExtremum upper a value) : SequenceExtremumExistsValue M upper (denote a) :=
  ⟨semanticObject (denote value) (isSet value), hv, h⟩

theorem sequenceExtremumValueOfCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a : M.Value) (r : ℝ)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hr : HasSequenceExtremumValue M upper a (M.number (r : ℂ))) :
    sequenceExtremumValue upper a=M.number (r : ℂ) := by
  classical
  have hm : M.mem (M.number (r : ℂ)) (denote (R (M := M))) := (M.real_members _).mpr ⟨r,rfl⟩
  let v : Obj (M := M) M.Value := semanticObject (M.number (r : ℂ)) (M.member_isSet hm)
  have hc : SequenceExtremumExistsValue M upper a := ⟨v,hm,hr⟩
  have hs := Classical.choose_spec hc
  obtain ⟨s, hv⟩ := (M.real_members _).mp hs.1
  have heq := sequenceExtremumUnique upper a s r hf (hv ▸ hs.2) hr
  unfold sequenceExtremumValue
  rw [dif_pos hc]
  exact hv.trans (congrArg (fun x : ℝ => M.number (x : ℂ)) heq)

theorem sequenceExtremumEqCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (upper : Bool) (p : Obj (M := M) (SequenceExtremumObj (M := M) upper α))
    (value : Obj (M := M) β) (hv : In value R)
    (h : HasSequenceExtremum upper p.val.sequence value) : Same p value := by
  let r := NativeBridge.asReal value hv
  have hr := NativeBridge.asReal_spec value hv
  change sequenceExtremumValue upper (denote p.val.sequence)=denote value
  exact (sequenceExtremumValueOfCandidate upper (denote p.val.sequence) r p.wd.1 (hr ▸ h)).trans hr.symm

theorem sequenceExtremumInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (upper : Bool)
    (p : Obj (M := M) (SequenceExtremumObj (M := M) upper α)) : In p R := by
  classical
  change M.mem (sequenceExtremumValue upper (denote p.val.sequence)) (denote R)
  unfold sequenceExtremumValue
  rw [dif_pos p.wd.2]
  exact (Classical.choose_spec p.wd.2).1

theorem sequenceExtremumCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (upper : Bool) (a : Obj (M := M) α) (v : Obj (M := M) β) (w : Obj (M := M) γ)
    (hf : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In v R) (hw : In w R)
    (h1 : HasSequenceExtremum upper a v) (h2 : HasSequenceExtremum upper a w) : Same v w := by
  let r := NativeBridge.asReal v hv
  let s := NativeBridge.asReal w hw
  have hr := NativeBridge.asReal_spec v hv
  have hs := NativeBridge.asReal_spec w hw
  change denote v=denote w
  exact hr.trans ((congrArg (fun x : ℝ => M.number (x : ℂ))
    (sequenceExtremumUnique upper (denote a) r s hf (hr ▸ h1) (hs ▸ h2))).trans hs.symm)

end Litex

namespace Litex

theorem sequenceExtremumSelected {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (upper : Bool)
    (p : Obj (M := M) (SequenceExtremumObj (M := M) upper α)) :
    HasSequenceExtremum upper p.val.sequence p := by
  classical
  change HasSequenceExtremumValue M upper (denote p.val.sequence) (sequenceExtremumValue upper (denote p.val.sequence))
  unfold sequenceExtremumValue
  rw [dif_pos p.wd.2]
  exact (Classical.choose_spec p.wd.2).2

theorem sequenceExtremumRay_numbers {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (r epsilon y : ℝ) :
    M.mem (M.number (y : ℂ)) (sequenceExtremumRayValue upper (M.number (r : ℂ)) (M.number (epsilon : ℂ))) ↔
      (if upper then y<r+epsilon else r-epsilon<y) := by
  rw [sequenceExtremumRayValue,F.sep_members]
  have hy : M.mem (M.number (y : ℂ)) (denote (R (M := M))) := (M.real_members _).mpr ⟨y,rfl⟩
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, M.add_numbers, M.sub_numbers,
    ← Complex.ofReal_add, ← Complex.ofReal_sub,realLtValue_numbers] <;>
    exact ⟨fun h => h.2.2, fun h => ⟨hy,hy,h⟩⟩

theorem sequenceExtremumOfLimit {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (upper : Bool) (a : Obj (M := M) α) (value : Obj (M := M) β)
    (hf : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In value R) (h : HasSequenceLimit a value) : HasSequenceExtremum upper a value := by
  let r := NativeBridge.asReal value hv
  have hr : denote value=M.number (r : ℂ) := NativeBridge.asReal_spec value hv
  have hlimit : HasSequenceLimitValue M (denote a) (M.number (r : ℂ)) := hr ▸ h
  change HasSequenceExtremumValue M upper (denote a) (denote value)
  rw [hr]
  constructor
  · intro epsilon hepsilon
    let e : Obj (M := M) M.Value := semanticObject epsilon (M.member_isSet hepsilon)
    let delta := NativeBridge.asReal e (inRPos_real e hepsilon)
    have hevalue : epsilon=M.number (delta : ℂ) := NativeBridge.asReal_spec e (inRPos_real e hepsilon)
    obtain ⟨cut,hcut,htail⟩ := hlimit epsilon hepsilon
    refine ⟨cut,hcut,?_⟩
    intro index hindex
    obtain ⟨n,hn,hnval,hle⟩ := sequenceTail_index cut hcut index hindex
    have hdist := sequenceLimitAtIndex (denote a) r delta cut n hn hf hcut hle (hevalue ▸ htail)
    obtain ⟨y,hy,hdist⟩ := hdist
    apply (F.preimage_mem_iff _ (isSet (NPos (M := M))) hf).mpr
    refine ⟨((F.sep_members _ _ _).mp hindex).1,?_⟩
    rw [hnval,hy,hevalue]
    apply (sequenceExtremumRay_numbers upper r delta y).mpr
    have hbounds := abs_lt.mp hdist
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  · intro epsilon hepsilon cutoff hcutoff
    let e : Obj (M := M) M.Value := semanticObject epsilon (M.member_isSet hepsilon)
    let delta := NativeBridge.asReal e (inRPos_real e hepsilon)
    have hevalue : epsilon=M.number (delta : ℂ) := NativeBridge.asReal_spec e (inRPos_real e hepsilon)
    let cut : Obj (M := M) M.Value := semanticObject cutoff (M.member_isSet hcutoff)
    obtain ⟨bound,hbound,htail⟩ := hlimit epsilon hepsilon
    let c := NativeBridge.asNat cut (inNPos_natural cut hcutoff)
    let b := NativeBridge.asNat bound (inNPos_natural bound hbound)
    let n := Nat.max c b+1
    have hn : 0<n := by dsimp [n];omega
    have hcn : c≤n := Nat.le_trans (Nat.le_max_left c b) (Nat.le_succ _)
    have hbn : b≤n := Nat.le_trans (Nat.le_max_right c b) (Nat.le_succ _)
    have hnmem := numberInNPosOfEq (M := M) (n : ℂ) n rfl hn
    let index : Obj (M := M) M.Value := semanticObject (M.number (n : ℂ)) (M.member_isSet hnmem)
    obtain ⟨y,hy,hdist⟩ := sequenceLimitAtIndex (denote a) r delta bound n hn hf hbound hbn (hevalue ▸ htail)
    refine ⟨index,hnmem,?_,?_⟩
    · refine ⟨(c : ℝ),(n : ℝ),?_,?_,?_⟩
      · have hcv : cutoff=M.number (c : ℂ) := NativeBridge.asNat_spec cut (inNPos_natural cut hcutoff)
        simpa only [Complex.ofReal_natCast] using hcv
      · change M.number (n : ℂ)=M.number ((n : ℝ) : ℂ)
        rw [Complex.ofReal_natCast]
      · exact_mod_cast hcn
    · change (if upper then RealLtValue M (M.subValue (M.number (r : ℂ)) epsilon) (F.callValue (denote a) (M.number (n : ℂ))) else RealLtValue M (F.callValue (denote a) (M.number (n : ℂ))) (M.addValue (M.number (r : ℂ)) epsilon))
      rw [hy,hevalue]
      have hbounds := abs_lt.mp hdist
      cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, M.add_numbers,M.sub_numbers,
        ← Complex.ofReal_add,← Complex.ofReal_sub,realLtValue_numbers] <;> linarith

theorem sequenceExtremumConstant {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (upper : Bool) (a : Obj (M := M) α) (value : Obj (M := M) β)
    (hf : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In value R)
    (h : ∀ n, M.mem n (denote (NPos (M := M))) → F.callValue (denote a) n=denote value) :
    HasSequenceExtremum upper a value := by
  let r := NativeBridge.asReal value hv
  have hr := NativeBridge.asReal_spec value hv
  have ht : Filter.Tendsto (observeRealSequence (denote a)) Filter.atTop (nhds r) := by
    apply Metric.tendsto_atTop.mpr
    intro epsilon hepsilon
    refine ⟨1,?_⟩
    intro n hn
    have hnpos : 0<n := by omega
    have hobs : observeRealSequence (denote a) n=r := by
      unfold observeRealSequence
      have hcall : F.callValue (denote a) (M.number (n : ℂ))=denote value :=
        h _ (numberInNPosOfEq (n : ℂ) n rfl hnpos)
      rw [hcall,hr,observeRealValue_number]
    simpa only [hobs,dist_self] using hepsilon
  apply sequenceExtremumOfLimit upper a value hf hv
  change HasSequenceLimitValue M (denote a) (denote value)
  rw [hr]
  exact (sequenceLimit_iff_tendsto (denote a) r hf).mpr ht
end Litex



/-! Oriented Riemann integration uses the original closed-cell Darboux definition.
The integral selector requires verified existence; its fallback value cannot supply WD. -/
section RiemannIntegration

open scoped BigOperators

open MeasureTheory Set
namespace Litex.RiemannGeometry

noncomputable def step {ι : Type*} (s : Finset ι) (left right height : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, (Ioc (left i) (right i)).indicator (fun _ => height i) x

theorem stepIntegrable {ι : Type*} (s : Finset ι) (left right height : ι → ℝ) :
    Integrable (step s left right height) := by
  apply integrable_finsetSum
  intro i hi
  have hc : IntegrableOn (fun _ : ℝ => height i) (Ioc (left i) (right i)) volume := integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  exact (integrable_indicator_iff measurableSet_Ioc).mpr hc

theorem stepIntegral {ι : Type*} (s : Finset ι) (left right height : ι → ℝ)
    (ordered : ∀ i ∈ s, left i ≤ right i) :
    ∫ x, step s left right height x = ∑ i ∈ s, height i * (right i-left i) := by
  change (∫ x, ∑ i ∈ s, (Ioc (left i) (right i)).indicator (fun _ => height i) x) = _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator_const _ measurableSet_Ioc,Real.volume_real_Ioc_of_le (ordered i hi)]
    exact mul_comm _ _
  · intro i hi
    have hc : IntegrableOn (fun _ : ℝ => height i) (Ioc (left i) (right i)) volume := integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    exact (integrable_indicator_iff measurableSet_Ioc).mpr hc

theorem stepSumsMonotone {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (left right lower : ι → ℝ) (left' right' upper : κ → ℝ)
    (ordered : ∀ i ∈ s, left i ≤ right i)
    (ordered' : ∀ i ∈ t, left' i ≤ right' i)
    (h : ∀ x, step s left right lower x ≤ step t left' right' upper x) :
    (∑ i ∈ s, lower i * (right i-left i)) ≤ ∑ j ∈ t, upper j * (right' j-left' j) := by
  rw [← stepIntegral s left right lower ordered,← stepIntegral t left' right' upper ordered']
  exact integral_mono (stepIntegrable s left right lower) (stepIntegrable t left' right' upper) h

/-- The finite partition has exactly one cell containing each interior/right-end point. -/
theorem partitionCellUnique {n i j : ℕ} {p : ℕ → ℝ} {x : ℝ}
    (ordered : ∀ a b, a ≤ b → b ≤ n → p a ≤ p b)
    (hi : i < n) (hj : j < n)
    (hxi : x ∈ Ioc (p i) (p (i+1))) (hxj : x ∈ Ioc (p j) (p (j+1))) : i=j := by
  rcases lt_trichotomy i j with h | h | h
  · have hle := ordered (i+1) j (by omega) (by omega)
    exact False.elim (not_lt_of_ge (le_trans hxi.2 hle) hxj.1)
  · exact h
  · have hle := ordered (j+1) i (by omega) (by omega)
    exact False.elim (not_lt_of_ge (le_trans hxj.2 hle) hxi.1)

theorem partitionStepValue {n i : ℕ} {p height : ℕ → ℝ} {x : ℝ}
    (ordered : ∀ a b, a ≤ b → b ≤ n → p a ≤ p b)
    (hi : i < n) (hx : x ∈ Ioc (p i) (p (i+1))) :
    step (Finset.range n) p (fun j => p (j+1)) height x = height i := by
  unfold step
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j hj hne
    apply Set.indicator_of_notMem
    intro hxj
    exact hne (partitionCellUnique ordered (Finset.mem_range.mp hj) hi hxj hx)
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hi))

theorem partitionStepOutside {n : ℕ} {p height : ℕ → ℝ} {x : ℝ}
    (ordered : ∀ a b, a ≤ b → b ≤ n → p a ≤ p b)
    (hx : x ∉ Ioc (p 0) (p n)) :
    step (Finset.range n) p (fun j => p (j+1)) height x = 0 := by
  unfold step
  apply Finset.sum_eq_zero
  intro i hi
  apply Set.indicator_of_notMem
  intro hcell
  apply hx
  exact ⟨lt_of_le_of_lt (ordered 0 i (Nat.zero_le _) (by simpa using Nat.le_of_lt (Finset.mem_range.mp hi))) hcell.1,
    le_trans hcell.2 (ordered (i+1) n (Finset.mem_range.mp hi) (le_refl _))⟩

theorem partitionLowerUpper {n m : ℕ} {p q lower upper : ℕ → ℝ} {f : ℝ → ℝ}
    (ordered : ∀ a b, a ≤ b → b ≤ n → p a ≤ p b)
    (ordered' : ∀ a b, a ≤ b → b ≤ m → q a ≤ q b)
    (left : p 0=q 0) (right : p n=q m)
    (hl : ∀ i<n, ∀ x ∈ Ioc (p i) (p (i+1)), lower i ≤ f x)
    (hu : ∀ j<m, ∀ x ∈ Ioc (q j) (q (j+1)), f x ≤ upper j) :
    (∑ i ∈ Finset.range n, lower i*(p (i+1)-p i)) ≤
      ∑ j ∈ Finset.range m, upper j*(q (j+1)-q j) := by
  apply stepSumsMonotone
  · intro i hi
    exact ordered i (i+1) (by omega) (Finset.mem_range.mp hi)
  · intro j hj
    exact ordered' j (j+1) (by omega) (Finset.mem_range.mp hj)
  · intro x
    by_cases hx : x ∈ Ioc (p 0) (p n)
    · have hxp := Ioc_subset_biUnion_Ioc n p hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxp
      have hxq := Ioc_subset_biUnion_Ioc m q (show x ∈ Ioc (q 0) (q m) from by simpa [left,right] using hx)
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxq
      rw [partitionStepValue ordered (Finset.mem_range.mp hi) hxi,
        partitionStepValue ordered' (Finset.mem_range.mp hj) hxj]
      exact le_trans (hl i (Finset.mem_range.mp hi) x hxi) (hu j (Finset.mem_range.mp hj) x hxj)
    · rw [partitionStepOutside ordered hx,
        partitionStepOutside ordered' (show x ∉ Ioc (q 0) (q m) from by simpa [left,right] using hx)]

structure Enclosure (f : ℝ → ℝ) (a b : ℝ) where
  n : ℕ
  points : ℕ → ℝ
  lower : ℕ → ℝ
  upper : ℕ → ℝ
  ordered : ∀ i j, i ≤ j → j ≤ n → points i ≤ points j
  left : points 0 = a
  right : points n = b
  lower_bound : ∀ i<n, ∀ x ∈ Ioc (points i) (points (i+1)), lower i ≤ f x
  upper_bound : ∀ i<n, ∀ x ∈ Ioc (points i) (points (i+1)), f x ≤ upper i

noncomputable def Enclosure.lowerSum {f a b} (e : Enclosure f a b) : ℝ :=
  ∑ i ∈ Finset.range e.n, e.lower i*(e.points (i+1)-e.points i)
noncomputable def Enclosure.upperSum {f a b} (e : Enclosure f a b) : ℝ :=
  ∑ i ∈ Finset.range e.n, e.upper i*(e.points (i+1)-e.points i)

theorem Enclosure.compare {f a b} (e d : Enclosure f a b) : e.lowerSum ≤ d.upperSum := by
  exact partitionLowerUpper e.ordered d.ordered (e.left.trans d.left.symm)
    (e.right.trans d.right.symm) e.lower_bound d.upper_bound

def HasDarbouxValue (f : ℝ → ℝ) (a b value : ℝ) : Prop :=
  ∀ epsilon>0, ∃ e : Enclosure f a b,
    e.lowerSum ≤ value ∧ value ≤ e.upperSum ∧ e.upperSum-e.lowerSum<epsilon

theorem darbouxValuesEqual {f a b v w} (hv : HasDarbouxValue f a b v)
    (hw : HasDarbouxValue f a b w) : v=w := by
  have comparison : ∀ u z, HasDarbouxValue f a b u → HasDarbouxValue f a b z → u ≤ z := by
    intro u z hu hz
    by_contra h
    have gap : 0 < (u-z)/2 := by linarith
    obtain ⟨e,heL,heU,heW⟩ := hu _ gap
    obtain ⟨d,hdL,hdU,hdW⟩ := hz _ gap
    have order := e.compare d
    linarith
  exact le_antisymm (comparison v w hv hw) (comparison w v hw hv)

end Litex.RiemannGeometry

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- The source partition functions use an integer carrier and two guards. -/
noncomputable def riemannIndexDomain (lower upper : M.Value) : M.Value :=
  F.sepValue (M.standard .integer) (fun k => RealLeValue M lower k ∧ RealLeValue M k upper)

noncomputable def riemannIndexFnValue (lower upper : M.Value) : M.Value :=
  F.fnSetValue (riemannIndexDomain lower upper) (M.standard .real)

theorem riemannIndexDomain_number (lower upper k : ℤ) (hlo : lower ≤ k) (hhi : k ≤ upper) :
    M.mem (M.number (k : ℂ)) (riemannIndexDomain (M.number (lower : ℂ)) (M.number (upper : ℂ))) := by
  apply (F.sep_members _ _ _).mpr
  refine ⟨NativeBridge.numberInZ k, ?_, ?_⟩
  · exact (realLeValue_numbers (lower : ℝ) (k : ℝ)).mpr (by exact_mod_cast hlo)
  · exact (realLeValue_numbers (k : ℝ) (upper : ℝ)).mpr (by exact_mod_cast hhi)

theorem riemannIndexFn_call_real {f : M.Value} {lower upper k : ℤ}
    (hf : M.mem f (riemannIndexFnValue (M.number (lower : ℂ)) (M.number (upper : ℂ))))
    (hlo : lower ≤ k) (hhi : k ≤ upper) :
    M.mem (F.callValue f (M.number (k : ℂ))) (M.standard .real) :=
  F.call_mem _ _ _ _ hf (riemannIndexDomain_number lower upper k hlo hhi)

omit F in
theorem riemannRealObservation {x : M.Value} (hx : M.mem x (M.standard .real)) :
    x = M.number (observeRealValue x : ℂ) := by
  obtain ⟨r, rfl⟩ := (M.real_members x).mp hx
  rw [observeRealValue_number]

omit F in
theorem riemannRealLeObserve {x y : M.Value} (h : RealLeValue M x y) :
    observeRealValue x ≤ observeRealValue y := by
  obtain ⟨r, s, rfl, rfl, h⟩ := h
  simpa only [observeRealValue_number] using h

omit F in
theorem riemannRealLtObserve {x y : M.Value} (h : RealLtValue M x y) :
    observeRealValue x < observeRealValue y := by
  obtain ⟨r, s, rfl, rfl, h⟩ := h
  simpa only [observeRealValue_number] using h

noncomputable def riemannClosedIntervalValue (a b : M.Value) : M.Value :=
  F.sepValue (M.standard .real) (fun x => realBound true a x ∧ realBound true x b)

/-- The nine original source clauses, with the checked closed-cell bounds. -/
def DarbouxEnclosureValue (f a b n p lower upper : M.Value) : Prop :=
  RealLtValue M a b ∧ M.mem n (denote (NPos (M := M))) ∧
  M.mem p (riemannIndexFnValue (M.number 0) n) ∧
  M.mem lower (riemannIndexFnValue (M.number 1) n) ∧
  M.mem upper (riemannIndexFnValue (M.number 1) n) ∧
  F.callValue p (M.number 0) = a ∧ F.callValue p n = b ∧
  (∀ k, M.mem k (closedRangeValue (M.number 1) n) →
    RealLtValue M (F.callValue p (M.subValue k (M.number 1))) (F.callValue p k) ∧
    RealLeValue M a (F.callValue p (M.subValue k (M.number 1))) ∧
    RealLeValue M (F.callValue p k) b) ∧
  (∀ k, M.mem k (closedRangeValue (M.number 1) n) →
    ∀ x, M.mem x (riemannClosedIntervalValue a b) →
    RealLeValue M (F.callValue p (M.subValue k (M.number 1))) x →
    RealLeValue M x (F.callValue p k) →
    RealLeValue M (F.callValue lower k) (F.callValue f x) ∧
    RealLeValue M (F.callValue f x) (F.callValue upper k))

def riemannStepBody (p height k : M.Value) : M.Value :=
  M.mulValue (F.callValue height k)
    (M.subValue (F.callValue p k) (F.callValue p (M.subValue k (M.number 1))))

noncomputable def riemannStepSumValue (n p height : M.Value) : M.Value :=
  let domain := riemannIndexDomain (M.number 1) n
  let body := riemannStepBody p height
  let integrand := F.graphValue domain (M.standard .real) body
  M.number (nativeRangeAggregate false (NativeBridge.integerValue (M.number 1)) (NativeBridge.integerValue n)
    (fun k => NativeBridge.complexValue (F.callValue integrand (M.number (k : ℂ)))))

end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

noncomputable def darbouxNativeEnclosure {f p lower upper : M.Value} {a b : ℝ} {n : ℕ}
    (h : DarbouxEnclosureValue f (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number (n : ℂ)) p lower upper) : RiemannGeometry.Enclosure (observeRealFunction f) a b := by
  have hp := h.2.2.1
  have hp0 := h.2.2.2.2.2.1
  have hpn := h.2.2.2.2.2.2.1
  have order := h.2.2.2.2.2.2.2.1
  have bounds := h.2.2.2.2.2.2.2.2
  let points := fun k : ℕ => observeRealValue (F.callValue p (M.number (k : ℂ)))
  have index (k : ℕ) (hk : k < n) :
      M.mem (M.number ((k+1 : ℕ) : ℂ)) (closedRangeValue (M.number 1) (M.number (n : ℂ))) := by
    have h : M.mem (M.number ((k+1 : ℕ) : ℂ)) (closedRangeValue (M.number ((1 : ℤ) : ℂ)) (M.number ((n : ℤ) : ℂ))) := by
      apply (closedRangeValue_members (M := M) 1 (n : ℤ) _).mpr
      exact ⟨(k+1 : ℕ), by simp only [Int.cast_natCast], by omega, by omega⟩
    simpa only [Int.cast_one, Int.cast_natCast] using h
  have step (k : ℕ) (hk : k < n) : points k < points (k+1) ∧ a ≤ points k ∧ points (k+1) ≤ b := by
    have h := order _ (index k hk)
    simp only [M.sub_numbers, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [points, Nat.cast_add, Nat.cast_one] using riemannRealLtObserve h.1
    · simpa only [points, observeRealValue_number] using riemannRealLeObserve h.2.1
    · simpa only [points, Nat.cast_add, Nat.cast_one, observeRealValue_number] using riemannRealLeObserve h.2.2
  have ordered : ∀ i j, i ≤ j → j ≤ n → points i ≤ points j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ j hij ih =>
      intro hj
      exact le_trans (ih (by omega)) (step j (by omega)).1.le
  have value (k : ℕ) (hk : k ≤ n) : F.callValue p (M.number (k : ℂ)) = M.number (points k : ℂ) := by
    have hp' : M.mem p (riemannIndexFnValue (M.number ((0 : ℤ) : ℂ)) (M.number ((n : ℤ) : ℂ))) := by
      simpa only [Int.cast_zero, Int.cast_natCast] using hp
    apply riemannRealObservation
    simpa only [Int.cast_natCast] using riemannIndexFn_call_real (k := (k : ℤ)) hp' (by omega) (by omega)
  have cell (k : ℕ) (hk : k < n) (x : ℝ) (hx : x ∈ Set.Ioc (points k) (points (k+1))) :
      observeRealValue (F.callValue lower (M.number ((k+1 : ℕ) : ℂ))) ≤ observeRealFunction f x ∧
      observeRealFunction f x ≤ observeRealValue (F.callValue upper (M.number ((k+1 : ℕ) : ℂ))) := by
    have hxA : M.mem (M.number (x : ℂ)) (riemannClosedIntervalValue (M.number (a : ℂ)) (M.number (b : ℂ))) := by
      apply (F.sep_members _ _ _).mpr
      exact ⟨NativeBridge.numberInR x,
        (realLeValue_numbers a x).mpr (le_trans (step k hk).2.1 hx.1.le),
        (realLeValue_numbers x b).mpr (le_trans hx.2 (step k hk).2.2)⟩
    have hleft : RealLeValue M (F.callValue p (M.subValue (M.number ((k+1 : ℕ) : ℂ)) (M.number 1))) (M.number (x : ℂ)) := by
      simp only [M.sub_numbers, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      rw [value k (by omega)]
      exact (realLeValue_numbers _ _).mpr hx.1.le
    have hright : RealLeValue M (M.number (x : ℂ)) (F.callValue p (M.number ((k+1 : ℕ) : ℂ))) := by
      rw [value (k+1) (by omega)]
      exact (realLeValue_numbers _ _).mpr hx.2
    have h := bounds _ (index k hk) _ hxA hleft hright
    exact ⟨riemannRealLeObserve h.1, riemannRealLeObserve h.2⟩
  exact {
    n := n
    points := points
    lower := fun k => observeRealValue (F.callValue lower (M.number ((k+1 : ℕ) : ℂ)))
    upper := fun k => observeRealValue (F.callValue upper (M.number ((k+1 : ℕ) : ℂ)))
    ordered := ordered
    left := by simp only [points, Nat.cast_zero, hp0, observeRealValue_number]
    right := by change observeRealValue (F.callValue p (M.number (n : ℂ))) = b; rw [hpn, observeRealValue_number]
    lower_bound := fun k hk x hx => (cell k hk x hx).1
    upper_bound := fun k hk x hx => (cell k hk x hx).2
  }
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem riemannIndexDomain_members (lower upper : ℤ) (x : M.Value) :
    M.mem x (riemannIndexDomain (M.number (lower : ℂ)) (M.number (upper : ℂ))) ↔
      ∃ k : ℤ, x = M.number (k : ℂ) ∧ lower ≤ k ∧ k ≤ upper := by
  constructor
  · intro hx
    obtain ⟨hz, hlo, hhi⟩ := (F.sep_members _ _ _).mp hx
    obtain ⟨k, rfl⟩ := (M.integer_members _).mp hz
    refine ⟨k, rfl, ?_, ?_⟩
    · have h := (realLeValue_numbers (lower : ℝ) (k : ℝ)).mp hlo
      exact_mod_cast h
    · have h := (realLeValue_numbers (k : ℝ) (upper : ℝ)).mp hhi
      exact_mod_cast h
  · rintro ⟨k, rfl, hlo, hhi⟩
    exact riemannIndexDomain_number lower upper k hlo hhi

omit F in
theorem riemannSumShift (n : ℕ) (value : ℤ → ℂ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), value k) =
      ∑ k ∈ Finset.range n, value ((k : ℤ) + 1) := by
  symm
  refine Finset.sum_bij (fun k _ => (k : ℤ)+1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ hab
    omega
  · intro k hk
    have hk := Finset.mem_Icc.mp hk
    refine ⟨(k-1).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro _ _
    rfl

theorem riemannStepBody_number {n k : ℤ} {p height : M.Value}
    (hp : M.mem p (riemannIndexFnValue (M.number 0) (M.number (n : ℂ))))
    (hh : M.mem height (riemannIndexFnValue (M.number 1) (M.number (n : ℂ))))
    (hlo : 1 ≤ k) (hhi : k ≤ n) :
    riemannStepBody p height (M.number (k : ℂ)) = M.number
      (((observeRealValue (F.callValue height (M.number (k : ℂ)))) *
        (observeRealValue (F.callValue p (M.number (k : ℂ))) -
          observeRealValue (F.callValue p (M.number ((k-1 : ℤ) : ℂ)))) : ℝ) : ℂ) := by
  have hp' : M.mem p (riemannIndexFnValue (M.number ((0 : ℤ) : ℂ)) (M.number (n : ℂ))) := by simpa only [Int.cast_zero] using hp
  have hh' : M.mem height (riemannIndexFnValue (M.number ((1 : ℤ) : ℂ)) (M.number (n : ℂ))) := by simpa only [Int.cast_one] using hh
  have hheight := riemannRealObservation (riemannIndexFn_call_real hh' hlo hhi)
  have hright := riemannRealObservation (riemannIndexFn_call_real hp' (k := k) (by omega) hhi)
  have hleft := riemannRealObservation (riemannIndexFn_call_real hp' (k := k-1) (by omega) (by omega))
  have hprev : M.subValue (M.number (k : ℂ)) (M.number 1) = M.number ((k-1 : ℤ) : ℂ) := by
    rw [M.sub_numbers, Int.cast_sub, Int.cast_one]
  unfold riemannStepBody
  rw [hprev, hheight, hright, hleft, M.sub_numbers, M.mul_numbers,
    Complex.ofReal_mul, Complex.ofReal_sub]
  simp only [observeRealValue_number]

theorem riemannStepBody_real {n : ℤ} {p height : M.Value}
    (hp : M.mem p (riemannIndexFnValue (M.number 0) (M.number (n : ℂ))))
    (hh : M.mem height (riemannIndexFnValue (M.number 1) (M.number (n : ℂ)))) :
    ∀ x, M.mem x (riemannIndexDomain (M.number 1) (M.number (n : ℂ))) →
      M.mem (riemannStepBody p height x) (M.standard .real) := by
  intro x hx
  have hx' : M.mem x (riemannIndexDomain (M.number ((1 : ℤ) : ℂ)) (M.number (n : ℂ))) := by simpa only [Int.cast_one] using hx
  obtain ⟨k, rfl, hlo, hhi⟩ := (riemannIndexDomain_members 1 n x).mp hx'
  exact (M.real_members _).mpr ⟨_, riemannStepBody_number hp hh hlo hhi⟩

theorem riemannStepSumValue_nat {n : ℕ} {p height : M.Value}
    (hp : M.mem p (riemannIndexFnValue (M.number 0) (M.number (n : ℂ))))
    (hh : M.mem height (riemannIndexFnValue (M.number 1) (M.number (n : ℂ)))) :
    riemannStepSumValue (M.number (n : ℂ)) p height = M.number
      (((∑ k ∈ Finset.range n, observeRealValue (F.callValue height (M.number ((k+1 : ℕ) : ℂ))) *
        (observeRealValue (F.callValue p (M.number ((k+1 : ℕ) : ℂ))) -
          observeRealValue (F.callValue p (M.number (k : ℂ))))) : ℝ) : ℂ) := by
  have hp' : M.mem p (riemannIndexFnValue (M.number 0) (M.number ((n : ℤ) : ℂ))) := by simpa only [Int.cast_natCast] using hp
  have hh' : M.mem height (riemannIndexFnValue (M.number 1) (M.number ((n : ℤ) : ℂ))) := by simpa only [Int.cast_natCast] using hh
  have hn : NativeBridge.integerValue (M.number (n : ℂ)) = (n : ℤ) := by
    simpa only [Int.cast_natCast] using NativeBridge.integerValue_number (M := M) (n : ℤ)
  have h1 : NativeBridge.integerValue (M.number 1) = (1 : ℤ) := by
    simpa only [Int.cast_one] using NativeBridge.integerValue_number (M := M) (1 : ℤ)
  unfold riemannStepSumValue
  dsimp only
  rw [hn, h1]
  unfold nativeRangeAggregate
  simp only [Bool.false_eq_true, ite_false]
  apply congrArg M.number
  rw [riemannSumShift, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk := Finset.mem_range.mp hk
  have hx : M.mem (M.number ((((k : ℤ)+1 : ℤ)) : ℂ)) (riemannIndexDomain (M.number 1) (M.number (n : ℂ))) := by
    simpa only [Int.cast_one, Int.cast_natCast] using riemannIndexDomain_number (M := M) 1 n ((k : ℤ)+1) (by omega) (by omega)
  have hbody : ∀ x, M.mem x (riemannIndexDomain (M.number 1) (M.number (n : ℂ))) → M.mem (riemannStepBody p height x) (M.standard .real) := by
    simpa only [Int.cast_natCast] using riemannStepBody_real hp' hh'
  rw [F.call_graphValue _ _ _ hbody _ hx, riemannStepBody_number hp' hh' (by omega) (by omega), NativeBridge.complexValue_number]
  simp only [add_sub_cancel_right, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]
theorem darbouxLowerUpperValue {f p q lower upper lower' upper' : M.Value}
    {a b : ℝ} {n m : ℕ}
    (h : DarbouxEnclosureValue f (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number (n : ℂ)) p lower upper)
    (h' : DarbouxEnclosureValue f (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number (m : ℂ)) q lower' upper') :
    RealLeValue M (riemannStepSumValue (M.number (n : ℂ)) p lower)
      (riemannStepSumValue (M.number (m : ℂ)) q upper') := by
  rw [riemannStepSumValue_nat h.2.2.1 h.2.2.2.1,
    riemannStepSumValue_nat h'.2.2.1 h'.2.2.2.2.1]
  apply (realLeValue_numbers _ _).mpr
  exact (darbouxNativeEnclosure h).compare (darbouxNativeEnclosure h')
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- Preserve the source's existential objects and ordered clauses. -/
def DarbouxApproximationValue (f a b value : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) → RealLtValue M a b →
    ∃ n : Obj (M := M) M.Value, ∃ _ : In n NPos,
    ∃ p : Obj (M := M) M.Value, ∃ _ : M.mem (denote p) (riemannIndexFnValue (M.number 0) (denote n)),
    ∃ lower : Obj (M := M) M.Value, ∃ _ : M.mem (denote lower) (riemannIndexFnValue (M.number 1) (denote n)),
    ∃ upper : Obj (M := M) M.Value, ∃ _ : M.mem (denote upper) (riemannIndexFnValue (M.number 1) (denote n)),
    ∃ lowerSum : Obj (M := M) M.Value, ∃ _ : In lowerSum R,
    ∃ upperSum : Obj (M := M) M.Value, ∃ _ : In upperSum R,
    ∃ _ : DarbouxEnclosureValue f a b (denote n) (denote p) (denote lower) (denote upper),
    ∃ _ : denote lowerSum = riemannStepSumValue (denote n) (denote p) (denote lower),
    ∃ _ : denote upperSum = riemannStepSumValue (denote n) (denote p) (denote upper),
    ∃ _ : RealLeValue M (denote lowerSum) value,
    ∃ _ : RealLeValue M value (denote upperSum),
      RealLtValue M (M.subValue (denote upperSum) (denote lowerSum)) epsilon

theorem darbouxEnclosureCompare {f a b n m p q lower upper lower' upper' : M.Value}
    (h : DarbouxEnclosureValue f a b n p lower upper)
    (k : DarbouxEnclosureValue f a b m q lower' upper') :
    RealLeValue M (riemannStepSumValue n p lower) (riemannStepSumValue m q upper') := by
  obtain ⟨ar,br,ha,hb,_⟩ := h.1
  have hn := inNPos_natural (semanticObject n (M.member_isSet h.2.1)) h.2.1
  have hm := inNPos_natural (semanticObject m (M.member_isSet k.2.1)) k.2.1
  obtain ⟨nr,hnr⟩ := (M.natural_members n).mp hn
  obtain ⟨mr,hmr⟩ := (M.natural_members m).mp hm
  rw [ha,hb,hnr] at h
  rw [ha,hb,hmr] at k
  rw [hnr,hmr]
  exact darbouxLowerUpperValue h k

omit F in
theorem riemannObserveSub {x y : M.Value}
    (hx : M.mem x (M.standard .real)) (hy : M.mem y (M.standard .real)) :
    observeRealValue (M.subValue x y) = observeRealValue x - observeRealValue y := by
  obtain ⟨r,rfl⟩ := (M.real_members x).mp hx
  obtain ⟨s,rfl⟩ := (M.real_members y).mp hy
  rw [M.sub_numbers,←Complex.ofReal_sub]
  simp only [observeRealValue_number]

theorem darbouxApproximationObserveLe {f a b v w : M.Value}
    (hab : RealLtValue M a b)
    (hv : DarbouxApproximationValue f a b v)
    (hw : DarbouxApproximationValue f a b w) :
    observeRealValue v ≤ observeRealValue w := by
  by_contra hle
  let epsilon := (observeRealValue v-observeRealValue w)/2
  have he : 0<epsilon := by dsimp [epsilon]; linarith
  obtain ⟨n,_,p,_,l,_,u,_,ls,hls,us,hus,henc,hlsEq,husEq,hl,hu,hgap⟩ :=
    hv (M.number (epsilon : ℂ)) (numberInRPos epsilon he) hab
  obtain ⟨n',_,p',_,l',_,u',_,ls',hls',us',hus',henc',hlsEq',husEq',hl',hu',hgap'⟩ :=
    hw (M.number (epsilon : ℂ)) (numberInRPos epsilon he) hab
  have hc := darbouxEnclosureCompare henc henc'
  rw [←hlsEq,←husEq'] at hc
  have hc := riemannRealLeObserve hc
  have hl := riemannRealLeObserve hl
  have hu := riemannRealLeObserve hu
  have hl' := riemannRealLeObserve hl'
  have hu' := riemannRealLeObserve hu'
  have hgap := riemannRealLtObserve hgap
  have hgap' := riemannRealLtObserve hgap'
  rw [riemannObserveSub hus hls,observeRealValue_number] at hgap
  rw [riemannObserveSub hus' hls',observeRealValue_number] at hgap'
  dsimp [epsilon] at hgap hgap'
  linarith

theorem darbouxApproximationUnique {f a b v w : M.Value}
    (hab : RealLtValue M a b)
    (hvReal : M.mem v (M.standard .real)) (hwReal : M.mem w (M.standard .real))
    (hv : DarbouxApproximationValue f a b v)
    (hw : DarbouxApproximationValue f a b w) : v=w := by
  have h := le_antisymm (darbouxApproximationObserveLe hab hv hw)
    (darbouxApproximationObserveLe hab hw hv)
  rw [riemannRealObservation hvReal,riemannRealObservation hwReal,h]

noncomputable def riemannIntervalValue (a b : M.Value) : M.Value :=
  riemannClosedIntervalValue (minMaxValue false a b) (minMaxValue true a b)

noncomputable def riemannRestrictedRangeValue (f a b : M.Value) : M.Value :=
  F.rangeValue (F.graphValue (F.sepValue (riemannIntervalValue a b) (fun _ => True)) (M.standard .real) (F.callValue f))

noncomputable def riemannOrientedValue (a b value : M.Value) : M.Value :=
  M.mulValue (signValue (M.subValue b a)) value

/-- Real candidates satisfying all six source definition clauses. -/
def HasRiemannIntegralValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f a b value : M.Value) : Prop :=
  M.mem value (M.standard .real) ∧
  M.mem a (M.standard .real) ∧ M.mem b (M.standard .real) ∧
  (∀ x, M.mem x (riemannIntervalValue a b) → M.mem x (F.domainValue f)) ∧
  RealBoundedValue M (riemannRestrictedRangeValue f a b) ∧
  (a ≠ b ∨ value = M.number 0) ∧
  DarbouxApproximationValue f (minMaxValue false a b) (minMaxValue true a b)
    (riemannOrientedValue a b value)

omit F in
theorem riemannOrientedValue_number (a b v : ℝ) :
    riemannOrientedValue (M.number (a : ℂ)) (M.number (b : ℂ)) (M.number (v : ℂ)) =
      M.number ((Real.sign (b-a)*v : ℝ) : ℂ) := by
  rw [riemannOrientedValue,M.sub_numbers,←Complex.ofReal_sub,signValue_number,
    M.mul_numbers,←Complex.ofReal_mul]

theorem riemannIntegralCandidatesEqual (f a b v w : M.Value)
    (hv : HasRiemannIntegralValue M f a b v)
    (hw : HasRiemannIntegralValue M f a b w) : v=w := by
  by_cases hab : a=b
  · exact (hv.2.2.2.2.2.1.resolve_left (not_not.mpr hab)).trans
      (hw.2.2.2.2.2.1.resolve_left (not_not.mpr hab)).symm
  · obtain ⟨ar,rfl⟩ := (M.real_members a).mp hv.2.1
    obtain ⟨br,rfl⟩ := (M.real_members b).mp hv.2.2.1
    obtain ⟨vr,rfl⟩ := (M.real_members v).mp hv.1
    obtain ⟨wr,rfl⟩ := (M.real_members w).mp hw.1
    have habr : ar≠br := fun h => hab (by rw [h])
    have horder : Min.min ar br < Max.max ar br := by
      rcases lt_or_gt_of_ne habr with h | h
      · simpa only [min_eq_left h.le,max_eq_right h.le] using h
      · simpa only [min_eq_right h.le,max_eq_left h.le] using h
    have he := hv.2.2.2.2.2.2
    have ke := hw.2.2.2.2.2.2
    rw [minMaxValue_number,minMaxValue_number,riemannOrientedValue_number] at he ke
    simp only [Bool.false_eq_true,ite_false,ite_true] at he ke
    have equal := darbouxApproximationUnique ((realLtValue_numbers _ _).mpr horder)
      ((M.real_members _).mpr ⟨_,rfl⟩) ((M.real_members _).mpr ⟨_,rfl⟩) he ke
    have equal := Complex.ofReal_injective (M.number_injective equal)
    have hsign : Real.sign (br-ar) ≠ 0 := by
      rcases lt_or_gt_of_ne habr with h | h
      · rw [Real.sign_of_pos (sub_pos.mpr h)]; norm_num
      · rw [Real.sign_of_neg (sub_neg.mpr h)]; norm_num
    have same := mul_left_cancel₀ hsign equal
    rw [same]

end Litex


namespace Litex

def FunctionRiemannIntegrableValue (M : Semantics.{u}) [FunctionSemantics M]
    (f a b : M.Value) : Prop :=
  ∃ v : Obj (M := M) M.Value, ∃ _ : In v R, HasRiemannIntegralValue M f a b (denote v)

theorem riemannIntegralExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f a b v : M.Value) (h : HasRiemannIntegralValue M f a b v) :
    FunctionRiemannIntegrableValue M f a b :=
  ⟨semanticObject v (M.member_isSet h.1),h.1,h⟩

/-- The raw denotation is fixed independently of the supplied WD certificate. -/
noncomputable def riemannIntegralValue {M : Semantics.{u}} [FunctionSemantics M]
    (f a b : M.Value) : M.Value := by
  classical
  exact if h : ∃ v, HasRiemannIntegralValue M f a b v then Classical.choose h else M.number 0

theorem riemannIntegralValueSelected {M : Semantics.{u}} [FunctionSemantics M]
    (f a b : M.Value) (h : FunctionRiemannIntegrableValue M f a b) :
    HasRiemannIntegralValue M f a b (riemannIntegralValue f a b) := by
  classical
  obtain ⟨v,_,hv⟩ := h
  have hex : ∃ v, HasRiemannIntegralValue M f a b v := ⟨denote v,hv⟩
  unfold riemannIntegralValue
  rw [dif_pos hex]
  exact Classical.choose_spec hex

structure RiemannIntegralObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  function : Obj (M := M) α
  lower : Obj (M := M) β
  upper : Obj (M := M) γ

noncomputable instance riemannIntegralRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (RiemannIntegralObj (M := M) α β γ) where
  wd p := RealFunctionValue M (denote p.function) ∧ In p.lower R ∧ In p.upper R ∧
    (∀ x, M.mem x (riemannIntervalValue (denote p.lower) (denote p.upper)) →
      M.mem x (F.domainValue (denote p.function))) ∧
    FunctionRiemannIntegrableValue M (denote p.function) (denote p.lower) (denote p.upper)
  denote p := riemannIntegralValue (denote p.function) (denote p.lower) (denote p.upper)
  wd_isSet h := M.member_isSet (riemannIntegralValueSelected _ _ _ h.2.2.2.2).1

theorem riemannIntegralInReal {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RiemannIntegralObj (M := M) α β γ)) : In p R :=
  (riemannIntegralValueSelected _ _ _ p.wd.2.2.2.2).1

theorem riemannIntegralEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RiemannIntegralObj (M := M) α β γ)) (v : M.Value)
    (h : HasRiemannIntegralValue M (denote p.val.function) (denote p.val.lower) (denote p.val.upper) v) :
    denote p=v :=
  riemannIntegralCandidatesEqual _ _ _ _ _ (riemannIntegralValueSelected _ _ _ p.wd.2.2.2.2) h

theorem riemannIntegralZeroWidth {M : Semantics.{u}} [FunctionSemantics M]
    (f a value : M.Value) (h : HasRiemannIntegralValue M f a a value) : value=M.number 0 :=
  h.2.2.2.2.2.1.resolve_left (not_not.mpr rfl)

end Litex

end RiemannIntegration
