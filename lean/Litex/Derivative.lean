import Litex.Analysis

universe u v w x r

namespace Litex

def DerivativeInteriorValue (M : Semantics.{u}) [FunctionSemantics M]
    (f : M.Value) (point : ℝ) : Prop :=
  ∃ radius : ℝ, 0<radius ∧ ∀ x : ℝ, |x-point|<radius →
    M.mem (M.number (x : ℂ)) (FunctionSemantics.domainValue f)

def DerivativeEpsilonValue (M : Semantics.{u}) [FunctionSemantics M]
    (f : M.Value) (point value : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0<epsilon → ∃ delta : ℝ, 0<delta ∧ ∀ x : ℝ,
    M.mem (M.number (x : ℂ)) (FunctionSemantics.domainValue f) →
    0 < |x-point| → |x-point|<delta →
    |(observeRealFunction (M := M) f x-observeRealFunction (M := M) f point)/(x-point)-value|<epsilon

def HasDerivativeAtValue (M : Semantics.{u}) [FunctionSemantics M]
    (f point value : M.Value) : Prop :=
  ∃ p r : ℝ, point=M.number (p : ℂ) ∧ value=M.number (r : ℂ) ∧
    DerivativeInteriorValue M f p ∧ DerivativeEpsilonValue M f p r

def HasDerivativeAt {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (f : Obj (M := M) α) (point : Obj (M := M) β) (value : Obj (M := M) γ) : Prop :=
  HasDerivativeAtValue M (denote f) (denote point) (denote value)

theorem derivativeEpsilon_iff_hasDerivAt {M : Semantics.{u}} [FunctionSemantics M]
    (f : M.Value) (p r : ℝ) (hi : DerivativeInteriorValue M f p) :
    DerivativeEpsilonValue M f p r ↔ HasDerivAt (observeRealFunction (M := M) f) r p := by
  rw [hasDerivAt_iff_tendsto_slope,Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h epsilon hepsilon
    obtain ⟨delta,hdelta,hd⟩ := h epsilon hepsilon
    obtain ⟨radius,hradius,hr⟩ := hi
    refine ⟨Min.min delta radius,lt_min hdelta hradius,?_⟩
    intro x hx hnear
    have hxne : x≠p := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hx
    have hxd : |x-p|<delta := (lt_min_iff.mp (by simpa only [Real.dist_eq] using hnear)).1
    have hxr : |x-p|<radius := (lt_min_iff.mp (by simpa only [Real.dist_eq] using hnear)).2
    have hbound := hd x (hr x hxr) (abs_pos.mpr (sub_ne_zero.mpr hxne)) hxd
    simpa only [slope,smul_eq_mul,vsub_eq_sub,div_eq_mul_inv,Real.dist_eq,mul_comm] using hbound
  · intro h epsilon hepsilon
    obtain ⟨delta,hdelta,hd⟩ := h epsilon hepsilon
    refine ⟨delta,hdelta,?_⟩
    intro x _ hxpos hxnear
    have hxne : x≠p := sub_ne_zero.mp (abs_pos.mp hxpos)
    have hbound := hd (by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hxne)
      (by simpa only [Real.dist_eq] using hxnear)
    simpa only [slope,smul_eq_mul,vsub_eq_sub,div_eq_mul_inv,Real.dist_eq,mul_comm] using hbound
end Litex

namespace Litex

def DerivativeExistsValue (M : Semantics.{u}) [FunctionSemantics M]
    (f point : M.Value) : Prop :=
  ∃ value : Obj (M := M) M.Value, ∃ _ : In value R,
    HasDerivativeAtValue M f point (denote value)

theorem derivativeCandidatesUnique {M : Semantics.{u}} [FunctionSemantics M]
    (f point : M.Value) (r s : ℝ)
    (hr : HasDerivativeAtValue M f point (M.number (r : ℂ)))
    (hs : HasDerivativeAtValue M f point (M.number (s : ℂ))) : r=s := by
  obtain ⟨p,r',hp,hr',hi,hd⟩ := hr
  obtain ⟨q,s',hq,hs',hj,he⟩ := hs
  have hpq : p=q := Complex.ofReal_injective (M.number_injective (hp.symm.trans hq))
  have hrr : r=r' := Complex.ofReal_injective (M.number_injective hr')
  have hss : s=s' := Complex.ofReal_injective (M.number_injective hs')
  subst q
  have h1 := (derivativeEpsilon_iff_hasDerivAt f p r' hi).mp hd
  have h2 := (derivativeEpsilon_iff_hasDerivAt f p s' hj).mp he
  exact hrr.trans ((h1.unique h2).trans hss.symm)

-- Only WD-certified objects expose this denotation; object construction below
-- requires an existing derivative witness and never returns an invalid object.
noncomputable def derivativeValue {M : Semantics.{u}} [FunctionSemantics M]
    (f point : M.Value) : M.Value := by
  classical
  exact if h : DerivativeExistsValue M f point then denote (Classical.choose h) else M.number 0

structure DerivativeObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  function : Obj (M := M) α
  point : Obj (M := M) β

noncomputable instance derivativeRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (DerivativeObj (M := M) α β) where
  wd p := RealFunctionValue M (denote p.function) ∧
    M.mem (denote p.point) (F.domainValue (denote p.function)) ∧
    DerivativeExistsValue M (denote p.function) (denote p.point)
  denote p := derivativeValue (denote p.function) (denote p.point)
  wd_isSet {p} hp := by
    classical
    unfold derivativeValue
    rw [dif_pos hp.2.2]
    exact M.member_isSet (Classical.choose_spec hp.2.2).1

noncomputable def derivative {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (point : Obj (M := M) β)
    (hf : RealFunctionValue M (denote f))
    (hp : M.mem (denote point) (F.domainValue (denote f)))
    (he : DerivativeExistsValue M (denote f) (denote point)) :
    Obj (M := M) (DerivativeObj (M := M) α β) := ⟨⟨f,point⟩,hf,hp,he⟩

theorem derivativeExistsOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (f : Obj (M := M) α) (point : Obj (M := M) β) (value : Obj (M := M) γ)
    (hv : In value R) (h : HasDerivativeAt f point value) :
    DerivativeExistsValue M (denote f) (denote point) :=
  ⟨semanticObject (denote value) (isSet value),hv,h⟩

theorem derivativeValueOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point : M.Value) (r : ℝ)
    (h : HasDerivativeAtValue M f point (M.number (r : ℂ))) :
    derivativeValue f point=M.number (r : ℂ) := by
  classical
  have hm : M.mem (M.number (r : ℂ)) (denote (R (M := M))) := (M.real_members _).mpr ⟨r,rfl⟩
  let value : Obj (M := M) M.Value := semanticObject (M.number (r : ℂ)) (M.member_isSet hm)
  have hc : DerivativeExistsValue M f point := ⟨value,hm,h⟩
  have hs := Classical.choose_spec hc
  obtain ⟨s,hselected⟩ := (M.real_members _).mp hs.1
  have heq := derivativeCandidatesUnique f point s r (hselected ▸ hs.2) h
  unfold derivativeValue
  rw [dif_pos hc]
  exact hselected.trans (congrArg (fun x : ℝ => M.number (x : ℂ)) heq)

theorem derivativeEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (DerivativeObj (M := M) α β)) (value : Obj (M := M) γ)
    (hv : In value R) (h : HasDerivativeAt p.val.function p.val.point value) : Same p value := by
  let r := NativeBridge.asReal value hv
  have hr : denote value=M.number (r : ℂ) := NativeBridge.asReal_spec value hv
  change derivativeValue (denote p.val.function) (denote p.val.point)=denote value
  exact (derivativeValueOfCandidate (denote p.val.function) (denote p.val.point) r (hr ▸ h)).trans hr.symm

theorem derivativeInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (DerivativeObj (M := M) α β)) : In p R := by
  classical
  change M.mem (derivativeValue (denote p.val.function) (denote p.val.point)) (denote R)
  unfold derivativeValue
  rw [dif_pos p.wd.2.2]
  exact (Classical.choose_spec p.wd.2.2).1
end Litex

namespace Litex
noncomputable def derivativeQuotientBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point input : M.Value) : M.Value :=
  M.divValue (M.subValue (F.callValue f input) (F.callValue f point)) (M.subValue input point)

theorem derivativeQuotientBody_number {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f) (p x : ℝ)
    (hp : M.mem (M.number (p : ℂ)) (F.domainValue f))
    (hx : M.mem (M.number (x : ℂ)) (F.domainValue f)) (hne : x≠p) :
    derivativeQuotientBody f (M.number (p : ℂ)) (M.number (x : ℂ)) =
      M.number (((observeRealFunction f x-observeRealFunction f p)/(x-p) : ℝ) : ℂ) := by
  have hn : (x : ℂ)-(p : ℂ)≠0 := by
    rw [←Complex.ofReal_sub]
    exact_mod_cast sub_ne_zero.mpr hne
  unfold derivativeQuotientBody
  rw [observeRealFunction_spec f hf x hx,observeRealFunction_spec f hf p hp,
    M.sub_numbers,M.sub_numbers,M.div_numbers _ _ hn,←Complex.ofReal_sub,←Complex.ofReal_sub,←Complex.ofReal_div]

theorem derivativeQuotientGraph {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point value D : M.Value) (hf : RealFunctionValue M f) (hD : M.isSet D)
    (hDspec : ∀ x, M.mem x D ↔ M.mem x (F.domainValue f) ∧ M.subValue x point≠M.number 0)
    (h : HasDerivativeAtValue M f point value) :
    let q := F.graphValue D (M.standard .real) (derivativeQuotientBody f point)
    RealFunctionValue M q ∧ HasFiniteFunctionLimitValue M .both q point value := by
  obtain ⟨p,r,hpoint,hvalue,hi,he⟩ := h
  subst point
  subst value
  have hp : M.mem (M.number (p : ℂ)) (F.domainValue f) := by
    obtain ⟨radius,hradius,hd⟩ := hi
    exact hd p (by simpa only [sub_self,abs_zero] using hradius)
  have hinput : ∀ x, M.mem x (F.domainValue f) → M.mem x (M.standard .real) := by
    obtain ⟨signature,hfn,hreal,_⟩ := hf
    intro x hx
    exact hreal x ((F.domainValue_eq signature.domain_isSet hfn) ▸ hx)
  have hreturn : ∀ x, M.mem x D → M.mem (derivativeQuotientBody f (M.number (p : ℂ)) x) (M.standard .real) := by
    intro x hx
    obtain ⟨hx,hne⟩ := (hDspec x).mp hx
    obtain ⟨z,hz⟩ := (M.real_members _).mp (hinput x hx)
    subst x
    have hzp : z≠p := by
      intro hz
      subst z
      exact hne (by rw [M.sub_numbers,sub_self])
    rw [derivativeQuotientBody_number f hf p z hp hx hzp]
    exact (M.real_members _).mpr ⟨_,rfl⟩
  have hfn := F.graph_inFnSet D (M.standard .real) (derivativeQuotientBody f (M.number (p : ℂ))) hreturn
  have hdomain := F.domainValue_eq hD hfn
  constructor
  · exact ⟨FunctionSignature.ofDomain D (M.standard .real) hD (M.standard_isSet .real),hfn,
      (fun x hx => hinput x ((hDspec x).mp hx).1),fun _ hx => hx⟩
  · refine ⟨p,r,rfl,rfl,?_,?_⟩
    · intro radius hradius
      obtain ⟨delta,hdelta,hd⟩ := hi
      let step := Min.min radius delta / 2
      have hs : 0<step := by dsimp [step];exact div_pos (lt_min hradius hdelta) (by norm_num)
      have hsR : step<radius := by dsimp [step];have := min_le_left radius delta;linarith
      have hsD : step<delta := by dsimp [step];have := min_le_right radius delta;linarith
      have habs : |p+step-p|=step := by rw [add_sub_cancel_left,abs_of_pos hs]
      refine ⟨p+step,?_,?_,?_⟩
      · rw [hdomain]
        apply (hDspec _).mpr
        refine ⟨hd _ (by rw [habs];exact hsD),?_⟩
        rw [M.sub_numbers,←Complex.ofReal_sub]
        intro hz
        have heq : p+step-p=0 := Complex.ofReal_injective (M.number_injective (by simpa only [Complex.ofReal_zero] using hz))
        linarith
      · simpa only [finiteLimitDistance,habs] using hs
      · simpa only [finiteLimitDistance,habs] using hsR
    · intro epsilon hepsilon
      obtain ⟨delta,hdelta,hd⟩ := he epsilon hepsilon
      refine ⟨delta,hdelta,?_⟩
      intro x hx hxpos hxnear
      have hxd := (hDspec _).mp (hdomain ▸ hx)
      have hne : x≠p := sub_ne_zero.mp (abs_pos.mp hxpos)
      refine ⟨(observeRealFunction f x-observeRealFunction f p)/(x-p),?_,hd x hxd.1 hxpos hxnear⟩
      exact (F.call_graphValue D (M.standard .real) _ hreturn _ (hdomain ▸ hx)).trans
        (derivativeQuotientBody_number f hf p x hp hxd.1 hne)

def DerivativeInteriorClauseValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point : M.Value) : Prop :=
  ∃ radius : Obj (M := M) M.Value, ∃ _ : In radius RPos,
    ∀ input, M.mem input (continuityNeighborhoodValue .both (M.standard .real) point (denote radius)) →
      M.mem input (F.domainValue f)

theorem derivativeInterior_iff_clause {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (p : ℝ) :
    DerivativeInteriorValue M f p ↔ DerivativeInteriorClauseValue M f (M.number (p : ℂ)) := by
  constructor
  · rintro ⟨radius,hradius,hd⟩
    let r : Obj (M := M) M.Value := semanticObject (M.number (radius : ℂ))
      (M.member_isSet (numberInRPos radius hradius))
    refine ⟨r,numberInRPos radius hradius,?_⟩
    intro input hx
    have hxR := ((F.sep_members _ _ _).mp hx).1
    obtain ⟨x,hxval⟩ := (M.real_members _).mp hxR
    rw [hxval] at hx ⊢
    exact hd x ((continuityNeighborhood_numbers_iff .both (M.standard .real) p radius x).mp hx).2.2
  · rintro ⟨radius,hradius,hd⟩
    obtain ⟨r,hr,hrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
    refine ⟨r,hrpos,?_⟩
    intro x hx
    apply hd
    rw [hr]
    apply (continuityNeighborhood_numbers_iff .both (M.standard .real) p r x).mpr
    exact ⟨(M.real_members _).mpr ⟨x,rfl⟩,True.intro,hx⟩

theorem derivativeInteriorOfCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point value : M.Value) (h : HasDerivativeAtValue M f point value) :
    DerivativeInteriorClauseValue M f point := by
  obtain ⟨p,r,hp,_,hi,_⟩ := h
  rw [hp]
  exact (derivativeInterior_iff_clause f p).mp hi
end Litex

namespace Litex
theorem derivativeExistsValueOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    (f point value : M.Value) (h : HasDerivativeAtValue M f point value) :
    DerivativeExistsValue M f point := by
  have hc := h
  obtain ⟨p,r,_,hr,_,_⟩ := hc
  have hv : M.mem value (M.standard .real) := (M.real_members _).mpr ⟨r,hr⟩
  exact ⟨semanticObject value (M.member_isSet hv),hv,h⟩
end Litex

namespace Litex

theorem derivativeQuotientBody_real {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (p : ℝ) (hf : RealFunctionValue M f)
    (hp : M.mem (M.number (p : ℂ)) (F.domainValue f))
    (x : M.Value) (hx : M.mem x (F.domainValue f))
    (hne : M.subValue x (M.number (p : ℂ))≠M.number 0) :
    M.mem (derivativeQuotientBody f (M.number (p : ℂ)) x) (M.standard .real) := by
  have hfc := hf
  obtain ⟨signature,hfn,hreal,_⟩ := hfc
  obtain ⟨z,hz⟩ := (M.real_members _).mp (hreal _ ((F.domainValue_eq signature.domain_isSet hfn) ▸ hx))
  subst x
  have hzp : z≠p := by
    intro hz
    subst z
    exact hne (by rw [M.sub_numbers,sub_self])
  rw [derivativeQuotientBody_number f hf p z hp hx hzp]
  exact (M.real_members _).mpr ⟨_,rfl⟩

theorem derivativeOfQuotientGraph {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point value D : M.Value) (hf : RealFunctionValue M f) (hD : M.isSet D)
    (hDspec : ∀ x, M.mem x D ↔ M.mem x (F.domainValue f) ∧ M.subValue x point≠M.number 0)
    (hi : DerivativeInteriorClauseValue M f point)
    (h : HasFiniteFunctionLimitValue M .both
      (F.graphValue D (M.standard .real) (derivativeQuotientBody f point)) point value) :
    HasDerivativeAtValue M f point value := by
  obtain ⟨p,r,hpoint,hvalue,_,he⟩ := h
  subst point
  subst value
  have hint := (derivativeInterior_iff_clause f p).mpr hi
  have hp : M.mem (M.number (p : ℂ)) (F.domainValue f) := by
    obtain ⟨radius,hradius,hd⟩ := hint
    exact hd p (by simpa only [sub_self,abs_zero] using hradius)
  have hreturn : ∀ x, M.mem x D → M.mem (derivativeQuotientBody f (M.number (p : ℂ)) x) (M.standard .real) :=
    fun x hx => derivativeQuotientBody_real f p hf hp x ((hDspec x).mp hx).1 ((hDspec x).mp hx).2
  have hfn := F.graph_inFnSet D (M.standard .real) (derivativeQuotientBody f (M.number (p : ℂ))) hreturn
  have hdomain := F.domainValue_eq hD hfn
  refine ⟨p,r,rfl,rfl,hint,?_⟩
  intro epsilon hepsilon
  obtain ⟨delta,hdelta,hd⟩ := he epsilon hepsilon
  refine ⟨delta,hdelta,?_⟩
  intro x hx hxpos hxnear
  have hne : x≠p := sub_ne_zero.mp (abs_pos.mp hxpos)
  have hcomplex : (x : ℂ)-(p : ℂ)≠0 := by
    rw [←Complex.ofReal_sub]
    exact_mod_cast sub_ne_zero.mpr hne
  have hxD : M.mem (M.number (x : ℂ)) D := by
    apply (hDspec _).mpr
    refine ⟨hx,?_⟩
    rw [M.sub_numbers]
    exact fun hz => hcomplex (M.number_injective hz)
  obtain ⟨output,houtput,hestimate⟩ := hd x (hdomain.symm ▸ hxD) hxpos hxnear
  have hcall := (F.call_graphValue D (M.standard .real) _ hreturn _ hxD).trans
    (derivativeQuotientBody_number f hf p x hp hx hne)
  have heq := Complex.ofReal_injective (M.number_injective (houtput.symm.trans hcall))
  rw [← heq]
  exact hestimate

theorem derivativeInteriorOfExistence {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point : M.Value) (h : DerivativeExistsValue M f point) :
    DerivativeInteriorClauseValue M f point := by
  obtain ⟨value,_,hc⟩ := h
  exact derivativeInteriorOfCandidate f point (denote value) hc
end Litex

open Filter
open scoped Topology
namespace Litex

def SemanticDerivativeAtValue (M : Semantics.{u}) (raw : ℝ → M.Value)
    (point : ℝ) (coefficient : M.Value) : Prop :=
  ∃ derivative : ℝ, coefficient=M.number (derivative : ℂ) ∧ ∃ native : ℝ → ℝ,
    raw =ᶠ[𝓝 point] (fun x => M.number (native x : ℂ)) ∧ HasDerivAt native derivative point

theorem semanticDerivativeConstant {M : Semantics.{u}} (value : M.Value) (p : ℝ)
    (hv : M.mem value (M.standard .real)) :
    SemanticDerivativeAtValue M (fun _ => value) p (M.number 0) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp hv
  refine ⟨0,rfl,fun _ => r,Filter.Eventually.of_forall (fun _ => hr),hasDerivAt_const p r⟩

theorem semanticDerivativeVariable {M : Semantics.{u}} (p : ℝ) :
    SemanticDerivativeAtValue M (fun x => M.number (x : ℂ)) p (M.number 1) :=
  ⟨1,rfl,id,Filter.Eventually.of_forall (fun _ => rfl),hasDerivAt_id p⟩

theorem semanticDerivativeNeg {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ) (d : M.Value)
    (h : SemanticDerivativeAtValue M raw p d) :
    SemanticDerivativeAtValue M (fun x => M.negValue (raw x)) p (M.negValue d) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  refine ⟨-s,?_,fun x => -f x,?_,hd.neg⟩
  · rw [hs,M.neg_numbers,←Complex.ofReal_neg]
  · exact hf.mono fun x hx => by dsimp only; rw [hx,M.neg_numbers,←Complex.ofReal_neg]

theorem semanticDerivativeAdd {M : Semantics.{u}} (raw other : ℝ → M.Value)
    (p : ℝ) (d e : M.Value)
    (h : SemanticDerivativeAtValue M raw p d) (k : SemanticDerivativeAtValue M other p e) :
    SemanticDerivativeAtValue M (fun x => M.addValue (raw x) (other x)) p (M.addValue d e) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  obtain ⟨t,ht,g,hg,he⟩ := k
  refine ⟨s+t,?_,fun x => f x+g x,?_,hd.add he⟩
  · rw [hs,ht,M.add_numbers,←Complex.ofReal_add]
  · exact (hf.and hg).mono fun x hx => by dsimp only; rw [hx.1,hx.2,M.add_numbers,←Complex.ofReal_add]

theorem semanticDerivativeSub {M : Semantics.{u}} (raw other : ℝ → M.Value)
    (p : ℝ) (d e : M.Value)
    (h : SemanticDerivativeAtValue M raw p d) (k : SemanticDerivativeAtValue M other p e) :
    SemanticDerivativeAtValue M (fun x => M.subValue (raw x) (other x)) p (M.subValue d e) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  obtain ⟨t,ht,g,hg,he⟩ := k
  refine ⟨s-t,?_,fun x => f x-g x,?_,hd.sub he⟩
  · rw [hs,ht,M.sub_numbers,←Complex.ofReal_sub]
  · exact (hf.and hg).mono fun x hx => by dsimp only; rw [hx.1,hx.2,M.sub_numbers,←Complex.ofReal_sub]

theorem semanticDerivativeMul {M : Semantics.{u}} (raw other : ℝ → M.Value)
    (p : ℝ) (d e : M.Value)
    (h : SemanticDerivativeAtValue M raw p d) (k : SemanticDerivativeAtValue M other p e) :
    SemanticDerivativeAtValue M (fun x => M.mulValue (raw x) (other x)) p
      (M.addValue (M.mulValue d (other p)) (M.mulValue (raw p) e)) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  obtain ⟨t,ht,g,hg,he⟩ := k
  refine ⟨s*g p+f p*t,?_,fun x => f x*g x,?_,hd.mul he⟩
  · rw [hs,ht,hf.eq_of_nhds,hg.eq_of_nhds,M.mul_numbers,M.mul_numbers,M.add_numbers,
      ←Complex.ofReal_mul,←Complex.ofReal_mul,←Complex.ofReal_add]
  · exact (hf.and hg).mono fun x hx => by dsimp only; rw [hx.1,hx.2,M.mul_numbers,←Complex.ofReal_mul]

theorem semanticDerivativeCoefficient {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (a b : M.Value) (h : SemanticDerivativeAtValue M raw p a) (equal : a=b) :
    SemanticDerivativeAtValue M raw p b := equal ▸ h


theorem semanticDerivativeDiv {M : Semantics.{u}} (raw other : ℝ → M.Value)
    (p : ℝ) (d e : M.Value)
    (h : SemanticDerivativeAtValue M raw p d) (k : SemanticDerivativeAtValue M other p e)
    (hne : other p≠M.number 0) :
    SemanticDerivativeAtValue M (fun x => M.divValue (raw x) (other x)) p
      (M.divValue (M.divValue (M.subValue (M.mulValue d (other p)) (M.mulValue (raw p) e)) (other p)) (other p)) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  obtain ⟨t,ht,g,hg,he⟩ := k
  have hgp : g p≠0 := by
    intro hz
    apply hne
    rw [hg.eq_of_nhds,hz,Complex.ofReal_zero]
  have hcomplex : (g p : ℂ)≠0 := by exact_mod_cast hgp
  refine ⟨((s*g p-f p*t)/g p)/g p,?_,fun x => f x/g x,?_,?_⟩
  · rw [hs,ht,hf.eq_of_nhds,hg.eq_of_nhds,M.mul_numbers,M.mul_numbers,M.sub_numbers,
      M.div_numbers _ _ hcomplex,M.div_numbers _ _ hcomplex]
    simp only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_mul]
  · filter_upwards [hf,hg,he.continuousAt.eventually_ne hgp] with x hx hy hn
    rw [hx,hy,M.div_numbers _ _ (by exact_mod_cast hn),←Complex.ofReal_div]
  · have hmul : HasDerivAt (fun x => f x*(g x)⁻¹) (s*(g p)⁻¹+f p*(-t/g p^2)) p := hd.mul (he.inv hgp)
    convert hmul using 1
    · rfl
    · field_simp
      ring

noncomputable def derivativePowerIndexValue {M : Semantics.{u}} (exponent : M.Value) : M.Value :=
  M.subValue (minMaxValue true exponent (M.number 1)) (M.number 1)

theorem derivativePowerIndex_number {M : Semantics.{u}} (n : ℕ) :
    derivativePowerIndexValue (M.number (n : ℂ)) = M.number ((n-1 : ℕ) : ℂ) := by
  have hsafe : Max.max (n : ℝ) 1-1=((n-1 : ℕ) : ℝ) := by
    cases n with
    | zero => norm_num
    | succ k =>
      rw [max_eq_left (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))]
      simp only [Nat.succ_sub_one,Nat.cast_add,Nat.cast_one]
      ring
  change M.subValue (minMaxValue true (M.number ((n : ℝ) : ℂ)) (M.number ((1 : ℝ) : ℂ)))
    (M.number ((1 : ℝ) : ℂ))=M.number ((n-1 : ℕ) : ℂ)
  rw [minMaxValue_number,M.sub_numbers,←Complex.ofReal_sub]
  simp only [ite_true,hsafe,Complex.ofReal_natCast]

theorem semanticDerivativePower {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (d exponent : M.Value) (n : ℕ) (hn : exponent=M.number (n : ℂ))
    (h : SemanticDerivativeAtValue M raw p d) :
    SemanticDerivativeAtValue M (fun x => M.powValue (raw x) exponent) p
      (M.mulValue (M.mulValue exponent (M.powValue (raw p) (derivativePowerIndexValue exponent))) d) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  refine ⟨(n : ℝ)*f p^(n-1)*s,?_,fun x => f x^n,?_,hd.pow n⟩
  · rw [hn,derivativePowerIndex_number,hf.eq_of_nhds,M.pow_numbers_nat,hs,M.mul_numbers,M.mul_numbers]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]
  · exact hf.mono fun x hx => by
      dsimp only
      rw [hx,hn,M.pow_numbers_nat,←Complex.ofReal_pow]


theorem derivativeInteriorOfOpenDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point domain : M.Value) (p : ℝ) (hp : point=M.number (p : ℂ))
    (hD : domain=F.domainValue f) (hpoint : M.mem point domain)
    (hopen : IsOpen {x : ℝ | M.mem (M.number (x : ℂ)) domain}) :
    DerivativeInteriorClauseValue M f point := by
  rw [hp] at hpoint ⊢
  apply (derivativeInterior_iff_clause f p).mp
  obtain ⟨radius,hradius,hd⟩ := Metric.isOpen_iff.mp hopen p hpoint
  refine ⟨radius,hradius,?_⟩
  intro x hx
  rw [←hD]
  apply hd
  simpa only [Metric.mem_ball,Real.dist_eq] using hx

theorem realDomainOpen {M : Semantics.{u}} :
    IsOpen {x : ℝ | M.mem (M.number (x : ℂ)) (M.standard .real)} := by
  have heq : {x : ℝ | M.mem (M.number (x : ℂ)) (M.standard .real)}=Set.univ := by
    ext x
    exact iff_true_intro ((M.real_members _).mpr ⟨x,rfl⟩)
  rw [heq]
  exact isOpen_univ

theorem positiveRealDomainOpen {M : Semantics.{u}} [F : FunctionSemantics M] :
    IsOpen {x : ℝ | M.mem (M.number (x : ℂ)) (denote (RPos (M := M)))} := by
  have heq : {x : ℝ | M.mem (M.number (x : ℂ)) (denote (RPos (M := M)))}=Set.Ioi 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨_,r,hr,hpositive⟩ := (positiveReal_members _).mp hx
      have hxr := Complex.ofReal_injective (M.number_injective hr)
      exact hxr.symm ▸ hpositive
    · intro hx
      exact (positiveReal_members _).mpr ⟨(M.real_members _).mpr ⟨x,rfl⟩,x,rfl,hx⟩
  rw [heq]
  exact isOpen_Ioi

theorem negativeRealDomainOpen {M : Semantics.{u}} [F : FunctionSemantics M] :
    IsOpen {x : ℝ | M.mem (M.number (x : ℂ)) (denote (RNeg (M := M)))} := by
  have heq : {x : ℝ | M.mem (M.number (x : ℂ)) (denote (RNeg (M := M)))}=Set.Iio 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨_,r,hr,hnegative⟩ := (F.sep_members _ _ _).mp hx
      have hxr := Complex.ofReal_injective (M.number_injective hr)
      exact hxr.symm ▸ hnegative
    · intro hx
      exact (F.sep_members _ _ _).mpr ⟨(M.real_members _).mpr ⟨x,rfl⟩,x,rfl,hx⟩
  rw [heq]
  exact isOpen_Iio

theorem nonzeroRealDomainOpen {M : Semantics.{u}} [F : FunctionSemantics M] :
    IsOpen {x : ℝ | M.mem (M.number (x : ℂ)) (denote (RStar (M := M)))} := by
  have heq : {x : ℝ | M.mem (M.number (x : ℂ)) (denote (RStar (M := M)))}=({0} : Set ℝ)ᶜ := by
    ext x
    change M.mem (M.number (x : ℂ)) (F.sepValue (M.standard .real) (fun y => y≠M.number 0)) ↔ x≠0
    rw [F.sep_members]
    constructor
    · rintro ⟨_,hne⟩ hx
      exact hne (by rw [hx,Complex.ofReal_zero])
    · intro hx
      refine ⟨(M.real_members _).mpr ⟨x,rfl⟩,?_⟩
      intro he
      exact hx (Complex.ofReal_injective (M.number_injective (by simpa only [Complex.ofReal_zero] using he)))
  rw [heq]
  exact isClosed_singleton.isOpen_compl

theorem derivativeOfSemanticFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point coefficient : M.Value) (p : ℝ) (raw : ℝ → M.Value)
    (hp : point=M.number (p : ℂ)) (hi : DerivativeInteriorClauseValue M f point)
    (hbody : ∀ x : ℝ, M.mem (M.number (x : ℂ)) (F.domainValue f) →
      F.callValue f (M.number (x : ℂ))=raw x)
    (h : SemanticDerivativeAtValue M raw p coefficient) :
    HasDerivativeAtValue M f point coefficient := by
  obtain ⟨d,hd,native,hnative,hderivative⟩ := h
  rw [hp] at hi
  have hint := (derivativeInterior_iff_clause f p).mpr hi
  refine ⟨p,d,hp,hd,hint,?_⟩
  apply (derivativeEpsilon_iff_hasDerivAt f p d hint).mpr
  apply hderivative.congr_of_eventuallyEq
  obtain ⟨radius,hradius,hnear⟩ := hint
  have hlocal : ∀ᶠ x in 𝓝 p, M.mem (M.number ((x : ℝ) : ℂ)) (F.domainValue f) :=
    Metric.eventually_nhds_iff.mpr ⟨radius,hradius,fun x hx => hnear x (by simpa only [Real.dist_eq] using hx)⟩
  filter_upwards [hlocal,hnative] with x hx heq
  unfold observeRealFunction
  rw [hbody x hx,heq,observeRealValue_number]
end Litex

namespace Litex
theorem derivativeCandidateInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (f : Obj (M := M) α) (point : Obj (M := M) β) (value : Obj (M := M) γ)
    (h : HasDerivativeAt f point value) : In value R := by
  obtain ⟨p,r,_,hr,_,_⟩ := h
  exact (M.real_members _).mpr ⟨r,hr⟩
end Litex

namespace Litex
variable {M : Semantics.{u}}

theorem integerModValueIdempotent (a m : M.Value)
    (ha : M.mem a (M.standard .integer))
    (hm : M.mem m (M.standard .integer)) :
    integerDivisionValue false (integerDivisionValue false a m) m =
      integerDivisionValue false a m := by
  obtain ⟨a, rfl⟩ := (M.integer_members _).mp ha
  obtain ⟨m, rfl⟩ := (M.integer_members _).mp hm
  simp only [integerDivisionValue_numbers, Bool.false_eq_true, if_false, Int.emod_emod]

theorem integerModAddCongr (a b c d m n : M.Value)
    (ha : M.mem a (M.standard .integer))
    (hb : M.mem b (M.standard .integer))
    (hc : M.mem c (M.standard .integer))
    (hd : M.mem d (M.standard .integer))
    (hm : M.mem m (M.standard .integer))
    (hmn : m = n)
    (hac : integerDivisionValue false a m = integerDivisionValue false c n)
    (hbd : integerDivisionValue false b m = integerDivisionValue false d n) :
    integerDivisionValue false (M.addValue a b) m =
      integerDivisionValue false (M.addValue c d) n := by
  cases hmn
  obtain ⟨a, rfl⟩ := (M.integer_members _).mp ha
  obtain ⟨b, rfl⟩ := (M.integer_members _).mp hb
  obtain ⟨c, rfl⟩ := (M.integer_members _).mp hc
  obtain ⟨d, rfl⟩ := (M.integer_members _).mp hd
  obtain ⟨m, rfl⟩ := (M.integer_members _).mp hm
  simp only [M.add_numbers, ← Int.cast_add, integerDivisionValue_numbers] at hac hbd ⊢
  have ha : Int.ModEq m a c := Int.cast_injective (M.number_injective hac)
  have hb : Int.ModEq m b d := Int.cast_injective (M.number_injective hbd)
  exact congrArg M.number (congrArg (fun z : ℤ => (z : ℂ)) (Int.ModEq.add ha hb))

theorem integerModSubCongr (a b c d m n : M.Value)
    (ha : M.mem a (M.standard .integer))
    (hb : M.mem b (M.standard .integer))
    (hc : M.mem c (M.standard .integer))
    (hd : M.mem d (M.standard .integer))
    (hm : M.mem m (M.standard .integer))
    (hmn : m = n)
    (hac : integerDivisionValue false a m = integerDivisionValue false c n)
    (hbd : integerDivisionValue false b m = integerDivisionValue false d n) :
    integerDivisionValue false (M.subValue a b) m =
      integerDivisionValue false (M.subValue c d) n := by
  cases hmn
  obtain ⟨a, rfl⟩ := (M.integer_members _).mp ha
  obtain ⟨b, rfl⟩ := (M.integer_members _).mp hb
  obtain ⟨c, rfl⟩ := (M.integer_members _).mp hc
  obtain ⟨d, rfl⟩ := (M.integer_members _).mp hd
  obtain ⟨m, rfl⟩ := (M.integer_members _).mp hm
  simp only [M.sub_numbers, ← Int.cast_sub, integerDivisionValue_numbers] at hac hbd ⊢
  have ha : Int.ModEq m a c := Int.cast_injective (M.number_injective hac)
  have hb : Int.ModEq m b d := Int.cast_injective (M.number_injective hbd)
  exact congrArg M.number (congrArg (fun z : ℤ => (z : ℂ)) (Int.ModEq.sub ha hb))

theorem integerModMulCongr (a b c d m n : M.Value)
    (ha : M.mem a (M.standard .integer))
    (hb : M.mem b (M.standard .integer))
    (hc : M.mem c (M.standard .integer))
    (hd : M.mem d (M.standard .integer))
    (hm : M.mem m (M.standard .integer))
    (hmn : m = n)
    (hac : integerDivisionValue false a m = integerDivisionValue false c n)
    (hbd : integerDivisionValue false b m = integerDivisionValue false d n) :
    integerDivisionValue false (M.mulValue a b) m =
      integerDivisionValue false (M.mulValue c d) n := by
  cases hmn
  obtain ⟨a, rfl⟩ := (M.integer_members _).mp ha
  obtain ⟨b, rfl⟩ := (M.integer_members _).mp hb
  obtain ⟨c, rfl⟩ := (M.integer_members _).mp hc
  obtain ⟨d, rfl⟩ := (M.integer_members _).mp hd
  obtain ⟨m, rfl⟩ := (M.integer_members _).mp hm
  simp only [M.mul_numbers, ← Int.cast_mul, integerDivisionValue_numbers] at hac hbd ⊢
  have ha : Int.ModEq m a c := Int.cast_injective (M.number_injective hac)
  have hb : Int.ModEq m b d := Int.cast_injective (M.number_injective hbd)
  exact congrArg M.number (congrArg (fun z : ℤ => (z : ℂ)) (Int.ModEq.mul ha hb))

end Litex

open Filter
open scoped Topology
namespace Litex

theorem semanticDerivativeUnary {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (d : M.Value) (operation slope : M.Value → M.Value) (native nativeSlope : ℝ → ℝ)
    (hoperation : ∀ r : ℝ, operation (M.number (r : ℂ))=M.number (native r : ℂ))
    (hslope : ∀ r : ℝ, slope (M.number (r : ℂ))=M.number (nativeSlope r : ℂ))
    (hnative : HasDerivAt native (nativeSlope (observeRealValue (raw p))) (observeRealValue (raw p)))
    (h : SemanticDerivativeAtValue M raw p d) :
    SemanticDerivativeAtValue M (fun x => operation (raw x)) p (M.mulValue (slope (raw p)) d) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  have hp : observeRealValue (raw p)=f p := by rw [hf.eq_of_nhds,observeRealValue_number]
  rw [hp] at hnative
  refine ⟨nativeSlope (f p)*s,?_,fun x => native (f x),?_,hnative.comp p hd⟩
  · rw [hf.eq_of_nhds,hslope,hs,M.mul_numbers,←Complex.ofReal_mul]
  · exact hf.mono fun x hx => by
      dsimp only
      rw [hx,hoperation]

theorem semanticDerivativeExp {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (d : M.Value) (h : SemanticDerivativeAtValue M raw p d) :
    SemanticDerivativeAtValue M (fun x => realUnaryValue Real.exp (raw x)) p
      (M.mulValue (realUnaryValue Real.exp (raw p)) d) :=
  semanticDerivativeUnary raw p d (realUnaryValue Real.exp) (realUnaryValue Real.exp)
    Real.exp Real.exp (realUnaryValue_number _) (realUnaryValue_number _)
    (Real.hasDerivAt_exp _) h

theorem semanticDerivativeSin {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (d : M.Value) (h : SemanticDerivativeAtValue M raw p d) :
    SemanticDerivativeAtValue M (fun x => realUnaryValue Real.sin (raw x)) p
      (M.mulValue (realUnaryValue Real.cos (raw p)) d) :=
  semanticDerivativeUnary raw p d (realUnaryValue Real.sin) (realUnaryValue Real.cos)
    Real.sin Real.cos (realUnaryValue_number _) (realUnaryValue_number _)
    (Real.hasDerivAt_sin _) h

theorem semanticDerivativeCos {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (d : M.Value) (h : SemanticDerivativeAtValue M raw p d) :
    SemanticDerivativeAtValue M (fun x => realUnaryValue Real.cos (raw x)) p
      (M.mulValue (M.negValue (realUnaryValue Real.sin (raw p))) d) := by
  apply semanticDerivativeUnary raw p d (realUnaryValue Real.cos)
    (fun x => M.negValue (realUnaryValue Real.sin x)) Real.cos (fun x => -Real.sin x)
    (realUnaryValue_number _)
  · intro r
    rw [realUnaryValue_number,M.neg_numbers,←Complex.ofReal_neg]
  · exact Real.hasDerivAt_cos _
  · exact h

theorem semanticDerivativeLn {M : Semantics.{u}} [FunctionSemantics M]
    (raw : ℝ → M.Value) (p : ℝ) (d : M.Value)
    (positive : M.mem (raw p) (denote (RPos (M := M))))
    (h : SemanticDerivativeAtValue M raw p d) :
    SemanticDerivativeAtValue M (fun x => realUnaryValue Real.log (raw x)) p (M.divValue d (raw p)) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  obtain ⟨_,r,hr,hpos⟩ := (positiveReal_members _).mp positive
  have hfp : f p=r := Complex.ofReal_injective (M.number_injective (hf.eq_of_nhds.symm.trans hr))
  have hn : (r : ℂ)≠0 := by exact_mod_cast hpos.ne'
  refine ⟨s/r,?_,fun x => Real.log (f x),?_,?_⟩
  · rw [hs,hr,M.div_numbers _ _ hn,←Complex.ofReal_div]
  · exact hf.mono fun x hx => by dsimp only;rw [hx,realUnaryValue_number]
  · have hlog := (Real.hasDerivAt_log (hfp ▸ hpos.ne')).comp p hd
    apply hlog.congr_deriv
    rw [hfp,div_eq_mul_inv]
    exact mul_comm _ _

theorem semanticDerivativeSqrt {M : Semantics.{u}} [FunctionSemantics M]
    (raw : ℝ → M.Value) (p : ℝ) (d : M.Value)
    (positive : M.mem (raw p) (denote (RPos (M := M))))
    (h : SemanticDerivativeAtValue M raw p d) :
    SemanticDerivativeAtValue M (fun x => sqrtValue (raw x)) p
      (M.divValue (M.divValue d (M.number 2)) (sqrtValue (raw p))) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  obtain ⟨_,r,hr,hpos⟩ := (positiveReal_members _).mp positive
  have hfp : f p=r := Complex.ofReal_injective (M.number_injective (hf.eq_of_nhds.symm.trans hr))
  have hsqrt : Real.sqrt r≠0 := (Real.sqrt_pos.mpr hpos).ne'
  have hn : (Real.sqrt r : ℂ)≠0 := by exact_mod_cast hsqrt
  refine ⟨s/2/Real.sqrt r,?_,fun x => Real.sqrt (f x),?_,?_⟩
  · rw [hs,hr,sqrtValue_number,M.div_numbers _ _ (by norm_num),M.div_numbers _ _ hn]
    simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  · exact hf.mono fun x hx => by dsimp only;rw [hx,sqrtValue_number]
  · have hsqrtNative := (Real.hasDerivAt_sqrt (hfp ▸ hpos.ne')).comp p hd
    apply hsqrtNative.congr_deriv
    rw [hfp]
    field_simp

theorem semanticDerivativeDropUnit {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (coefficient : M.Value) (real : M.mem coefficient (M.standard .real))
    (h : SemanticDerivativeAtValue M raw p (M.mulValue coefficient (M.number 1))) :
    SemanticDerivativeAtValue M raw p coefficient := by
  apply semanticDerivativeCoefficient raw p _ coefficient h
  obtain ⟨r,hr⟩ := (M.real_members _).mp real
  rw [hr,M.mul_numbers,mul_one]
end Litex

open Filter
open scoped Topology
namespace Litex

theorem semanticDerivativeValuePoint {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (d : M.Value) (h : SemanticDerivativeAtValue M raw p d) :
    raw p=M.number (observeRealValue (raw p) : ℂ) := by
  obtain ⟨s,_,f,hf,_⟩ := h
  rw [hf.eq_of_nhds,observeRealValue_number]

theorem semanticDerivativeOfCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point value : M.Value) (p : ℝ) (hp : point=M.number (p : ℂ))
    (hf : RealFunctionValue M f) (h : HasDerivativeAtValue M f point value) :
    SemanticDerivativeAtValue M (fun x => F.callValue f (M.number (x : ℂ))) p value := by
  obtain ⟨q,r,hq,hr,hi,he⟩ := h
  have hqp : q=p := Complex.ofReal_injective (M.number_injective (hq.symm.trans hp))
  subst q
  refine ⟨r,hr,observeRealFunction f,?_,(derivativeEpsilon_iff_hasDerivAt f p r hi).mp he⟩
  obtain ⟨radius,hradius,hd⟩ := hi
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨radius,hradius,?_⟩
  intro x hx
  exact observeRealFunction_spec f hf x (hd x (by simpa only [Real.dist_eq] using hx))

theorem semanticDerivativeCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    (raw : ℝ → M.Value) (outer : M.Value) (p : ℝ) (d e : M.Value)
    (h : SemanticDerivativeAtValue M raw p d)
    (k : SemanticDerivativeAtValue M (fun x => F.callValue outer (M.number (x : ℂ)))
      (observeRealValue (raw p)) e) :
    SemanticDerivativeAtValue M (fun x => F.callValue outer (raw x)) p (M.mulValue e d) := by
  obtain ⟨s,hs,f,hf,hd⟩ := h
  obtain ⟨t,ht,g,hg,he⟩ := k
  have hp : observeRealValue (raw p)=f p := by rw [hf.eq_of_nhds,observeRealValue_number]
  rw [hp] at hg he
  refine ⟨t*s,?_,fun x => g (f x),?_,he.comp p hd⟩
  · rw [ht,hs,M.mul_numbers,←Complex.ofReal_mul]
  · filter_upwards [hf,hg.comp_tendsto hd.continuousAt] with x hx houter
    rw [hx]
    exact houter

theorem semanticDerivativeDropLeftUnit {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (coefficient : M.Value) (real : M.mem coefficient (M.standard .real))
    (h : SemanticDerivativeAtValue M raw p (M.mulValue (M.number 1) coefficient)) :
    SemanticDerivativeAtValue M raw p coefficient := by
  apply semanticDerivativeCoefficient raw p _ coefficient h
  obtain ⟨r,hr⟩ := (M.real_members _).mp real
  rw [hr,M.mul_numbers,one_mul]

theorem derivativeSelectedCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (DerivativeObj (M := M) α β)) :
    HasDerivativeAtValue M (denote p.val.function) (denote p.val.point) (denote p) := by
  obtain ⟨value,hvalue,h⟩ := p.wd.2.2
  have heq := derivativeEqCandidate p value hvalue h
  exact (congrArg (HasDerivativeAtValue M (denote p.val.function) (denote p.val.point)) heq.symm).mp h
end Litex

namespace Litex
open Filter
open scoped Topology

def SemanticContinuousAtValue (M : Semantics.{u}) (raw : ℝ → M.Value) (p : ℝ) : Prop :=
  ∃ native : ℝ → ℝ, raw =ᶠ[𝓝 p] (fun x => M.number (native x : ℂ)) ∧ ContinuousAt native p

theorem semanticContinuousOfDerivative {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (d : M.Value) (h : SemanticDerivativeAtValue M raw p d) : SemanticContinuousAtValue M raw p := by
  obtain ⟨_,_,f,hf,hd⟩ := h
  exact ⟨f,hf,hd.continuousAt⟩

theorem semanticContinuousConstant {M : Semantics.{u}} (value : M.Value) (p : ℝ)
    (real : M.mem value (M.standard .real)) : SemanticContinuousAtValue M (fun _ => value) p := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp real
  exact ⟨fun _ => r,Filter.Eventually.of_forall (fun _ => hr),continuousAt_const⟩

theorem semanticContinuousVariable {M : Semantics.{u}} (p : ℝ) :
    SemanticContinuousAtValue M (fun x => M.number (x : ℂ)) p :=
  ⟨id,Filter.Eventually.of_forall (fun _ => rfl),continuousAt_id⟩

theorem semanticContinuousUnary {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (operation : M.Value → M.Value) (native : ℝ → ℝ)
    (law : ∀ r : ℝ, operation (M.number (r : ℂ))=M.number (native r : ℂ))
    (continuous : ContinuousAt native (observeRealValue (raw p)))
    (h : SemanticContinuousAtValue M raw p) :
    SemanticContinuousAtValue M (fun x => operation (raw x)) p := by
  obtain ⟨f,hf,hc⟩ := h
  have hp : observeRealValue (raw p)=f p := by rw [hf.eq_of_nhds,observeRealValue_number]
  rw [hp] at continuous
  refine ⟨fun x => native (f x),?_,continuous.comp hc⟩
  exact hf.mono fun x hx => by dsimp only;rw [hx,law]

theorem semanticContinuousNeg {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) : SemanticContinuousAtValue M (fun x => M.negValue (raw x)) p := by
  apply semanticContinuousUnary raw p M.negValue (fun r => -r)
  · intro r;rw [M.neg_numbers,←Complex.ofReal_neg]
  · exact continuousAt_id.neg
  · exact h

theorem semanticContinuousAbs {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) : SemanticContinuousAtValue M (fun x => absValue (raw x)) p :=
  semanticContinuousUnary raw p absValue (fun r : ℝ => |r|) absValue_number continuous_abs.continuousAt h

theorem semanticContinuousExp {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) :
    SemanticContinuousAtValue M (fun x => realUnaryValue Real.exp (raw x)) p :=
  semanticContinuousUnary raw p (realUnaryValue Real.exp) Real.exp
    (fun r => realUnaryValue_number Real.exp r) Real.continuous_exp.continuousAt h

theorem semanticContinuousSin {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) :
    SemanticContinuousAtValue M (fun x => realUnaryValue Real.sin (raw x)) p :=
  semanticContinuousUnary raw p (realUnaryValue Real.sin) Real.sin
    (fun r => realUnaryValue_number Real.sin r) Real.continuous_sin.continuousAt h

theorem semanticContinuousCos {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) :
    SemanticContinuousAtValue M (fun x => realUnaryValue Real.cos (raw x)) p :=
  semanticContinuousUnary raw p (realUnaryValue Real.cos) Real.cos
    (fun r => realUnaryValue_number Real.cos r) Real.continuous_cos.continuousAt h

theorem semanticContinuousLn {M : Semantics.{u}} [F : FunctionSemantics M]
    (raw : ℝ → M.Value) (p : ℝ) (positive : M.mem (raw p) (denote (RPos (M := M))))
    (h : SemanticContinuousAtValue M raw p) :
    SemanticContinuousAtValue M (fun x => realUnaryValue Real.log (raw x)) p := by
  apply semanticContinuousUnary raw p (realUnaryValue Real.log) Real.log
    (fun r => realUnaryValue_number Real.log r) _ h
  obtain ⟨_,r,hr,hrpos⟩ := (positiveReal_members _).mp positive
  have hp : observeRealValue (raw p)=r := by rw [hr,observeRealValue_number]
  rw [hp]
  exact Real.continuousAt_log (ne_of_gt hrpos)

theorem semanticContinuousSqrt {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) :
    SemanticContinuousAtValue M (fun x => sqrtValue (raw x)) p :=
  semanticContinuousUnary raw p sqrtValue Real.sqrt sqrtValue_number
    Real.continuous_sqrt.continuousAt h

theorem semanticContinuousAdd {M : Semantics.{u}} (raw other : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) (k : SemanticContinuousAtValue M other p) :
    SemanticContinuousAtValue M (fun x => M.addValue (raw x) (other x)) p := by
  obtain ⟨f,hf,hc⟩ := h
  obtain ⟨g,hg,hd⟩ := k
  refine ⟨fun x => f x+g x,?_,hc.add hd⟩
  exact (hf.and hg).mono fun x hx => by dsimp only;rw [hx.1,hx.2,M.add_numbers,←Complex.ofReal_add]

theorem semanticContinuousSub {M : Semantics.{u}} (raw other : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) (k : SemanticContinuousAtValue M other p) :
    SemanticContinuousAtValue M (fun x => M.subValue (raw x) (other x)) p := by
  obtain ⟨f,hf,hc⟩ := h
  obtain ⟨g,hg,hd⟩ := k
  refine ⟨fun x => f x-g x,?_,hc.sub hd⟩
  exact (hf.and hg).mono fun x hx => by dsimp only;rw [hx.1,hx.2,M.sub_numbers,←Complex.ofReal_sub]

theorem semanticContinuousMul {M : Semantics.{u}} (raw other : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) (k : SemanticContinuousAtValue M other p) :
    SemanticContinuousAtValue M (fun x => M.mulValue (raw x) (other x)) p := by
  obtain ⟨f,hf,hc⟩ := h
  obtain ⟨g,hg,hd⟩ := k
  refine ⟨fun x => f x*g x,?_,hc.mul hd⟩
  exact (hf.and hg).mono fun x hx => by dsimp only;rw [hx.1,hx.2,M.mul_numbers,←Complex.ofReal_mul]

theorem semanticContinuousDiv {M : Semantics.{u}} (raw other : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) (k : SemanticContinuousAtValue M other p)
    (nonzero : other p≠M.number 0) :
    SemanticContinuousAtValue M (fun x => M.divValue (raw x) (other x)) p := by
  obtain ⟨f,hf,hc⟩ := h
  obtain ⟨g,hg,hd⟩ := k
  have hgp : g p≠0 := by intro hz;apply nonzero;rw [hg.eq_of_nhds,hz,Complex.ofReal_zero]
  refine ⟨fun x => f x/g x,?_,hc.div hd hgp⟩
  filter_upwards [hf,hg,hd.eventually_ne hgp] with x hx hy hn
  rw [hx,hy,M.div_numbers _ _ (by exact_mod_cast hn),←Complex.ofReal_div]

theorem semanticContinuousPower {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (exponent : M.Value) (n : ℕ) (hn : exponent=M.number (n : ℂ))
    (h : SemanticContinuousAtValue M raw p) :
    SemanticContinuousAtValue M (fun x => M.powValue (raw x) exponent) p := by
  obtain ⟨f,hf,hc⟩ := h
  refine ⟨fun x => f x^n,?_,hc.pow n⟩
  exact hf.mono fun x hx => by dsimp only;rw [hx,hn,M.pow_numbers_nat,←Complex.ofReal_pow]

theorem semanticContinuousLt {M : Semantics.{u}} (raw other : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) (k : SemanticContinuousAtValue M other p)
    (less : RealLtValue M (raw p) (other p)) :
    ∀ᶠ x in 𝓝 p, RealLtValue M (raw x) (other x) := by
  obtain ⟨f,hf,hc⟩ := h
  obtain ⟨g,hg,hd⟩ := k
  have hp : f p<g p := (realLtValue_numbers _ _).mp (by rwa [hf.eq_of_nhds,hg.eq_of_nhds] at less)
  have he := hc.eventually_lt hd hp
  filter_upwards [hf,hg,he] with x hx hy hxy
  rw [hx,hy]
  exact (realLtValue_numbers _ _).mpr hxy

theorem semanticContinuousNe {M : Semantics.{u}} (raw other : ℝ → M.Value) (p : ℝ)
    (h : SemanticContinuousAtValue M raw p) (k : SemanticContinuousAtValue M other p)
    (different : raw p≠other p) : ∀ᶠ x in 𝓝 p, raw x≠other x := by
  obtain ⟨f,hf,hc⟩ := h
  obtain ⟨g,hg,hd⟩ := k
  have hp : f p-g p≠0 := by
    intro he
    apply different
    rw [hf.eq_of_nhds,hg.eq_of_nhds,sub_eq_zero.mp he]
  filter_upwards [hf,hg,(hc.sub hd).eventually_ne hp] with x hx hy hxy
  intro he
  have hfg : f x=g x := Complex.ofReal_injective (M.number_injective (hx.symm.trans (he.trans hy)))
  exact hxy (sub_eq_zero.mpr hfg)

theorem semanticContinuousMembership {M : Semantics.{u}} (raw : ℝ → M.Value) (p : ℝ)
    (domain : M.Value) (h : SemanticContinuousAtValue M raw p) (member : M.mem (raw p) domain)
    (openDomain : IsOpen {x : ℝ | M.mem (M.number (x : ℂ)) domain}) :
    ∀ᶠ x in 𝓝 p, M.mem (raw x) domain := by
  obtain ⟨f,hf,hc⟩ := h
  have hp : M.mem (M.number (f p : ℂ)) domain := hf.eq_of_nhds ▸ member
  have he := hc (openDomain.mem_nhds hp)
  filter_upwards [hf,he] with x hx hy
  rw [hx]
  exact hy

theorem realNeighborhoodOfInteriorClause {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point : M.Value) (p : ℝ) (hp : point=M.number (p : ℂ))
    (h : ∃ radius : Obj (M := M) M.Value, ∃ _ : In radius RPos,
      ∀ input, M.mem input (continuityNeighborhoodValue .both (M.standard .real) point (denote radius)) →
        M.mem input domain) :
    ∀ᶠ x in 𝓝 p, M.mem (M.number ((x : ℝ) : ℂ)) domain := by
  obtain ⟨radius,hradius,hd⟩ := h
  obtain ⟨r,hr,hrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨r,hrpos,?_⟩
  intro x hx
  apply hd
  rw [hp,hr]
  apply (continuityNeighborhood_numbers_iff .both (M.standard .real) p r x).mpr
  exact ⟨(M.real_members _).mpr ⟨x,rfl⟩,True.intro,by simpa only [Real.dist_eq,finiteLimitDistance] using hx⟩

theorem derivativeInteriorOfNeighborhood {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point : M.Value) (p : ℝ) (hp : point=M.number (p : ℂ))
    (h : ∀ᶠ x in 𝓝 p, M.mem (M.number ((x : ℝ) : ℂ)) (F.domainValue f)) :
    DerivativeInteriorClauseValue M f point := by
  rw [hp]
  apply (derivativeInterior_iff_clause f p).mp
  obtain ⟨radius,hradius,hd⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨radius,hradius,fun x hx => hd (by simpa only [Real.dist_eq] using hx)⟩

end Litex

