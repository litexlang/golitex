import Litex.Multivariable

universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem realMultivariableInOwnDomain (f n : M.Value)
    (hf : RealMultivariableFunctionValue M f n) :
    M.mem f (F.fnSetValue (F.sepValue (F.domainValue f) (fun _ => True)) (M.standard .real)) := by
  obtain ⟨signature,hfn,_,hout⟩ := hf
  have domain := F.domainValue_eq signature.domain_isSet hfn
  have graph := (F.fnSet_members _ _ _).mp hfn
  apply (F.fnSet_members _ _ _).mpr
  constructor
  · intro p hp
    obtain ⟨x,hx,y,hy,hp⟩ := graph.1 p hp
    exact ⟨x,(F.sep_members _ _ _).mpr ⟨domain.symm ▸ hx,True.intro⟩,y,hout y hy,hp⟩
  · intro x hx
    exact graph.2 x (domain ▸ ((F.sep_members _ _ _).mp hx).1)

-- Only the original coordinate interior is needed to extend the derivative.
-- All sufficiently small inputs stay inside the checked source domain.
theorem partialDerivativeOfLocalAgreement
    (source target point n axis value : M.Value)
    (returnsSource : ∀ x, M.mem x (F.domainValue source) → M.mem (F.callValue source x) (M.standard .real))
    (returnsTarget : ∀ x, M.mem x (F.domainValue target) → M.mem (F.callValue target x) (M.standard .real))
    (pointSource : M.mem point (F.domainValue source))
    (pointTarget : M.mem point (F.domainValue target))
    (extend : ∀ x, M.mem x (F.domainValue source) → M.mem x (F.domainValue target))
    (same : ∀ x, M.mem x (F.domainValue source) → F.callValue source x=F.callValue target x)
    (h : HasPartialDerivativeAtValue M source point n axis value) :
    HasPartialDerivativeAtValue M target point n axis value := by
  obtain ⟨hi,p,r,hp,hr,ha,he⟩ := h
  have hp0 : p=0 := Complex.ofReal_injective (M.number_injective (hp.symm.trans (by simp)))
  subst p
  obtain ⟨radius,hradius,hnear⟩ := hi
  obtain ⟨rad,hrad,hradpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
  have lawsS := partialQuotientGraphLaws source point n axis returnsSource pointSource
  have lawsT := partialQuotientGraphLaws target point n axis returnsTarget pointTarget
  refine ⟨⟨radius,hradius,fun t ht hs => extend _ (hnear t ht hs)⟩,0,r,by simp,hr,?_,?_⟩
  · intro epsilon hepsilon
    obtain ⟨input,hinput,hpos,hsmall⟩ := ha epsilon hepsilon
    have hs := (lawsS.1 _).mp hinput
    exact ⟨input,(lawsT.1 _).mpr ⟨hs.1,hs.2.1,extend _ hs.2.2⟩,hpos,hsmall⟩
  · intro epsilon hepsilon
    obtain ⟨delta,hdelta,hcontrol⟩ := he epsilon hepsilon
    refine ⟨Min.min delta rad,lt_min hdelta hradpos,?_⟩
    intro input hinput hpos hsmall
    have bound : |input|<rad := by
      have := lt_of_lt_of_le hsmall (min_le_right delta rad)
      simpa only [finiteLimitDistance,sub_zero] using this
    have inputSource : M.mem (M.number (input : ℂ)) (F.domainValue (partialQuotientValue source point n axis)) := by
      apply (lawsS.1 _).mpr
      refine ⟨(M.real_members _).mpr ⟨input,rfl⟩,((lawsT.1 _).mp hinput).2.1,?_⟩
      apply hnear _ ((M.real_members _).mpr ⟨input,rfl⟩)
      rw [absValue_number,hrad]
      exact ⟨|input|,rad,rfl,rfl,bound⟩
    obtain ⟨output,houtput,herror⟩ := hcontrol input inputSource hpos (lt_of_lt_of_le hsmall (min_le_left _ _))
    refine ⟨output,?_,herror⟩
    rw [lawsS.2 _ inputSource] at houtput
    rw [lawsT.2 _ hinput]
    rw [same _ ((lawsS.1 _).mp inputSource).2.2,same point pointSource] at houtput
    exact houtput

theorem secondPartialOfFirstPartialFunction
    (f g point n firstAxis secondAxis value : M.Value)
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (sameDomain : F.domainValue g=F.domainValue f)
    (pointDomain : M.mem point (F.domainValue f))
    (first : ∀ x, M.mem x (F.domainValue f) →
      HasPartialDerivativeAtValue M f x n firstAxis (F.callValue g x))
    (second : HasPartialDerivativeAtValue M g point n secondAxis value) :
    HasSecondPartialAtValue M f point n firstAxis secondAxis value := by
  obtain ⟨signature,hfn,hinput,_⟩ := hf
  have domain := F.domainValue_eq signature.domain_isSet hfn
  have domainSet : M.isSet (F.domainValue f) := domain.symm ▸ signature.domain_isSet
  let A := semanticObject (F.domainValue f) domainSet
  have memberG : M.mem g (F.fnSetValue (F.sepValue (F.domainValue f) (fun _ => True)) (M.standard .real)) := by
    rw [←sameDomain]
    exact realMultivariableInOwnDomain g n hg
  let G := semanticObject g (M.member_isSet memberG)
  refine ⟨A,(F.power_members _ _).mpr ⟨domainSet,fun x hx => hinput x (domain ▸ hx)⟩,
    G,memberG,fun _ hx => hx,pointDomain,?_,second⟩
  intro x hx
  exact (F.sep_members _ _ _).mpr ⟨hx,hx,first x hx⟩

theorem firstPartialFunctionOfSecondPartial
    (f g point n firstAxis secondAxis value : M.Value)
    (hg : RealMultivariableFunctionValue M g n)
    (sameDomain : F.domainValue g=F.domainValue f)
    (first : ∀ x, M.mem x (F.domainValue f) →
      HasPartialDerivativeAtValue M f x n firstAxis (F.callValue g x))
    (second : HasSecondPartialAtValue M f point n firstAxis secondAxis value) :
    HasPartialDerivativeAtValue M g point n secondAxis value := by
  obtain ⟨A,_,G,hG,subset,pointA,localFirst,localSecond⟩ := second
  have domainG : F.domainValue (denote G)=F.sepValue (denote A) (fun _ => True) :=
    F.domainValue_eq (F.sep_isSet _ _ A.wd) hG
  have pointG : M.mem point (F.domainValue (denote G)) := by
    rw [domainG]
    exact (F.sep_members _ _ _).mpr ⟨pointA,True.intro⟩
  apply partialDerivativeOfLocalAgreement (denote G) g point n secondAxis value
    (fun x hx => F.call_mem _ _ _ _ hG (domainG ▸ hx))
    (fun x hx => multivariableFunctionReturnsReal g n x hg hx) pointG
    (sameDomain.symm ▸ subset point pointA) _ _ localSecond
  · intro x hx
    exact sameDomain.symm ▸ subset x ((F.sep_members _ _ _).mp (domainG ▸ hx)).1
  · intro x hx
    have hxA := ((F.sep_members _ _ _).mp (domainG ▸ hx)).1
    exact partialDerivativeCandidatesEqual f x n firstAxis _ _
      ((F.sep_members _ _ _).mp (localFirst x hxA)).2.choose_spec
      (first x (subset x hxA))

end Litex
