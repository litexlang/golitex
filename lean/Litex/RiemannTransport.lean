import Litex.Analysis

universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem riemannIntegralReverseCandidate (f a b value : M.Value)
    (h : HasRiemannIntegralValue M f a b value) :
    HasRiemannIntegralValue M f b a (M.mulValue (M.number (-1)) value) := by
  obtain ⟨ar,rfl⟩ := (M.real_members a).mp h.2.1
  obtain ⟨br,rfl⟩ := (M.real_members b).mp h.2.2.1
  obtain ⟨vr,rfl⟩ := (M.real_members value).mp h.1
  have negValue : M.mulValue (M.number (-1)) (M.number (vr : ℂ))=M.number ((-vr : ℝ) : ℂ) := by
    rw [M.mul_numbers]
    congr 1
    simp only [neg_mul,one_mul,Complex.ofReal_neg]
  rw [negValue]
  have ends (maximum : Bool) :
      minMaxValue maximum (M.number (br : ℂ)) (M.number (ar : ℂ))=
      minMaxValue maximum (M.number (ar : ℂ)) (M.number (br : ℂ)) := by
    rw [minMaxValue_number,minMaxValue_number]
    cases maximum <;> simp only [Bool.false_eq_true,ite_false,ite_true,min_comm,max_comm]
  have interval : riemannIntervalValue (M.number (br : ℂ)) (M.number (ar : ℂ))=
      riemannIntervalValue (M.number (ar : ℂ)) (M.number (br : ℂ)) := by
    unfold riemannIntervalValue
    rw [ends false,ends true]
  have oriented : riemannOrientedValue (M.number (br : ℂ)) (M.number (ar : ℂ)) (M.number ((-vr : ℝ) : ℂ))=
      riemannOrientedValue (M.number (ar : ℂ)) (M.number (br : ℂ)) (M.number (vr : ℂ)) := by
    rw [riemannOrientedValue_number,riemannOrientedValue_number]
    have reverse : ar-br=-(br-ar) := by ring
    rw [reverse,Real.sign_neg,neg_mul_neg]
  refine ⟨(M.real_members _).mpr ⟨-vr,rfl⟩,h.2.2.1,h.2.1,?_,?_,?_,?_⟩
  · rw [interval]
    exact h.2.2.2.1
  · unfold riemannRestrictedRangeValue
    rw [interval]
    exact h.2.2.2.2.1
  · rcases h.2.2.2.2.2.1 with different | zero
    · exact Or.inl (Ne.symm different)
    · have valueZero : vr=0 := Complex.ofReal_injective (M.number_injective zero)
      rw [valueZero,neg_zero]
      exact Or.inr rfl
  · rw [ends false,ends true,oriented]
    exact h.2.2.2.2.2.2

theorem darbouxEnclosureLocalAgreement (f g a b n p lower upper : M.Value)
    (equal : ∀ x, M.mem x (riemannClosedIntervalValue a b) → F.callValue f x=F.callValue g x)
    (h : DarbouxEnclosureValue f a b n p lower upper) :
    DarbouxEnclosureValue g a b n p lower upper := by
  obtain ⟨order,hn,hp,hl,hu,start,finish,partition,bounds⟩ := h
  refine ⟨order,hn,hp,hl,hu,start,finish,partition,?_⟩
  intro k hk x hx lowerBound upperBound
  rw [←equal x hx]
  exact bounds k hk x hx lowerBound upperBound

theorem darbouxApproximationLocalAgreement (f g a b value : M.Value)
    (equal : ∀ x, M.mem x (riemannClosedIntervalValue a b) → F.callValue f x=F.callValue g x)
    (h : DarbouxApproximationValue f a b value) :
    DarbouxApproximationValue g a b value := by
  intro epsilon hepsilon order
  obtain ⟨n,hn,p,hp,lower,hl,upper,hu,lowerSum,hls,upperSum,hus,enclosure,
    lowerEqual,upperEqual,below,above,gap⟩ := h epsilon hepsilon order
  exact ⟨n,hn,p,hp,lower,hl,upper,hu,lowerSum,hls,upperSum,hus,
    darbouxEnclosureLocalAgreement f g a b _ _ _ _ equal enclosure,
    lowerEqual,upperEqual,below,above,gap⟩

theorem riemannRestrictedRangeLocalAgreement (f g a b : M.Value)
    (realG : RealFunctionValue M g)
    (coverG : ∀ x, M.mem x (riemannIntervalValue a b) → M.mem x (F.domainValue g))
    (equal : ∀ x, M.mem x (riemannIntervalValue a b) → F.callValue f x=F.callValue g x) :
    riemannRestrictedRangeValue f a b=riemannRestrictedRangeValue g a b := by
  let D := F.sepValue (riemannIntervalValue a b) (fun _ => True)
  have returnsG (x : M.Value) (hx : M.mem x D) : M.mem (F.callValue g x) (M.standard .real) := by
    obtain ⟨signature,member,_,output⟩ := realG
    exact output _ (F.call_mem _ _ _ _ member
      ((F.domainValue_eq signature.domain_isSet member) ▸ coverG x ((F.sep_members _ _ _).mp hx).1))
  have returnsF (x : M.Value) (hx : M.mem x D) : M.mem (F.callValue f x) (M.standard .real) := by
    rw [equal x ((F.sep_members _ _ _).mp hx).1]
    exact returnsG x hx
  have graphF := FunctionSemantics.graph_inFnSet D (M.standard .real) (F.callValue f) returnsF
  have graphG := FunctionSemantics.graph_inFnSet D (M.standard .real) (F.callValue g) returnsG
  have graphs : F.graphValue D (M.standard .real) (F.callValue f)=
      F.graphValue D (M.standard .real) (F.callValue g) := by
    apply F.graph_ext D (M.standard .real) _ _ ((F.fnSet_members _ _ _).mp graphF)
      ((F.fnSet_members _ _ _).mp graphG)
    intro x y
    rw [FunctionSemantics.pair_mem_graph,FunctionSemantics.pair_mem_graph]
    constructor
    · rintro ⟨hx,hy,body⟩
      exact ⟨hx,hy,body.trans (equal x ((F.sep_members _ _ _).mp hx).1)⟩
    · rintro ⟨hx,hy,body⟩
      exact ⟨hx,hy,body.trans (equal x ((F.sep_members _ _ _).mp hx).1).symm⟩
  exact congrArg (FunctionSemantics.rangeValue (M := M)) graphs

theorem riemannIntegralLocalAgreement (f g a b value : M.Value)
    (realG : RealFunctionValue M g)
    (coverG : ∀ x, M.mem x (riemannIntervalValue a b) → M.mem x (F.domainValue g))
    (equal : ∀ x, M.mem x (riemannIntervalValue a b) → F.callValue f x=F.callValue g x)
    (h : HasRiemannIntegralValue M f a b value) :
    HasRiemannIntegralValue M g a b value := by
  refine ⟨h.1,h.2.1,h.2.2.1,coverG,?_,h.2.2.2.2.2.1,?_⟩
  · rw [←riemannRestrictedRangeLocalAgreement f g a b realG coverG equal]
    exact h.2.2.2.2.1
  · exact darbouxApproximationLocalAgreement f g _ _ _ equal h.2.2.2.2.2.2
end Litex

