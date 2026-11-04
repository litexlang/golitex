import Litex.Analysis

universe u v

namespace Litex

/-- A local composition with an outer function continuous at the inner limit. -/
theorem finiteFunctionLimitContinuousCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (f g out point centre : M.Value)
    (radius : Obj (M := M) α) (hradius : In radius RPos)
    (hg : RealFunctionValue M g) (hout : RealFunctionValue M out)
    (hcentre : M.mem centre (F.domainValue g))
    (hinner : HasFiniteFunctionLimitValue M .both f point centre)
    (haccumulation : RealAccumulationValue M .both (F.domainValue out) point)
    (houter : FunctionContinuousAtValue M .both g centre)
    (hlocal : ∀ input,
      M.mem input (finiteLimitNeighborhoodValue .both (F.domainValue out) point (denote radius)) →
      M.mem input (F.domainValue f) ∧
      M.mem (F.callValue f input) (F.domainValue g) ∧
      F.callValue out input = F.callValue g (F.callValue f input)) :
    HasFiniteFunctionLimitValue M .both out point (F.callValue g centre) := by
  obtain ⟨p,y,hp,hy,_,hinnerControl⟩ := hinner
  have hymem : M.mem (M.number (y : ℂ)) (F.domainValue g) := hy ▸ hcentre
  have houterControl := (functionContinuity_iff_epsilonReal .both g hg y hymem).mp (hy ▸ houter)
  refine ⟨p,observeRealFunction g y,hp,?_,?_,?_⟩
  · rw [hy]
    exact observeRealFunction_spec g hg y hymem
  · exact finiteFunctionAccumulationFromClause .both out point (F.domainValue out) p
      hout rfl hp (fun r hr => haccumulation (denote r) hr)
  · intro epsilon hepsilon
    obtain ⟨outerDelta,hOuterDelta,outerControl⟩ := houterControl epsilon hepsilon
    obtain ⟨innerDelta,hInnerDelta,innerControl⟩ := hinnerControl outerDelta hOuterDelta
    obtain ⟨r,hr,hrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
    refine ⟨Min.min r innerDelta,lt_min hrpos hInnerDelta,?_⟩
    intro x hx hpositive hnear
    have hlocalx : M.mem (M.number (x : ℂ))
        (finiteLimitNeighborhoodValue .both (F.domainValue out) point (denote radius)) := by
      rw [hp,hr]
      exact (finiteLimitNeighborhood_numbers_iff .both _ p r x).mpr
        ⟨hx,hpositive,lt_of_lt_of_le hnear (min_le_left _ _)⟩
    obtain ⟨hxinner,hxouter,heq⟩ := hlocal _ hlocalx
    obtain ⟨z,hz,hzy⟩ := innerControl x hxinner hpositive
      (lt_of_lt_of_le hnear (min_le_right _ _))
    have hzouter : M.mem (M.number (z : ℂ)) (F.domainValue g) := hz ▸ hxouter
    refine ⟨observeRealFunction g z,?_,?_⟩
    · rw [heq,hz]
      exact observeRealFunction_spec g hg z hzouter
    · exact outerControl z hzouter True.intro hzy

/-- The punctured outer-limit rule retains local avoidance of the outer centre. -/
theorem finiteFunctionLimitPuncturedCompose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (f g out point centre value : M.Value)
    (radius : Obj (M := M) α) (hradius : In radius RPos)
    (hout : RealFunctionValue M out)
    (hinner : HasFiniteFunctionLimitValue M .both f point centre)
    (haccumulation : RealAccumulationValue M .both (F.domainValue out) point)
    (houter : HasFiniteFunctionLimitValue M .both g centre value)
    (hlocal : ∀ input,
      M.mem input (finiteLimitNeighborhoodValue .both (F.domainValue out) point (denote radius)) →
      M.mem input (F.domainValue f) ∧
      M.mem (F.callValue f input) (F.domainValue g) ∧
      F.callValue f input ≠ centre ∧
      F.callValue out input = F.callValue g (F.callValue f input)) :
    HasFiniteFunctionLimitValue M .both out point value := by
  obtain ⟨p,y,hp,hy,_,hinnerControl⟩ := hinner
  obtain ⟨q,l,hq,hl,_,houterControl⟩ := houter
  have hyq : y=q := Complex.ofReal_injective (M.number_injective (hy.symm.trans hq))
  subst q
  refine ⟨p,l,hp,hl,?_,?_⟩
  · exact finiteFunctionAccumulationFromClause .both out point (F.domainValue out) p
      hout rfl hp (fun r hr => haccumulation (denote r) hr)
  · intro epsilon hepsilon
    obtain ⟨outerDelta,hOuterDelta,outerControl⟩ := houterControl epsilon hepsilon
    obtain ⟨innerDelta,hInnerDelta,innerControl⟩ := hinnerControl outerDelta hOuterDelta
    obtain ⟨r,hr,hrpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
    refine ⟨Min.min r innerDelta,lt_min hrpos hInnerDelta,?_⟩
    intro x hx hpositive hnear
    have hlocalx : M.mem (M.number (x : ℂ))
        (finiteLimitNeighborhoodValue .both (F.domainValue out) point (denote radius)) := by
      rw [hp,hr]
      exact (finiteLimitNeighborhood_numbers_iff .both _ p r x).mpr
        ⟨hx,hpositive,lt_of_lt_of_le hnear (min_le_left _ _)⟩
    obtain ⟨hxinner,hxouter,havoid,heq⟩ := hlocal _ hlocalx
    obtain ⟨z,hz,hzy⟩ := innerControl x hxinner hpositive
      (lt_of_lt_of_le hnear (min_le_right _ _))
    have hzouter : M.mem (M.number (z : ℂ)) (F.domainValue g) := hz ▸ hxouter
    have hz_ne_y : z≠y := by
      intro hz_eq_y
      apply havoid
      rw [hz,hz_eq_y,←hy]
    obtain ⟨result,hresult,hestimate⟩ := outerControl z hzouter
      (abs_pos.mpr (sub_ne_zero.mpr hz_ne_y)) hzy
    exact ⟨result,(heq.trans (by rw [hz])).trans hresult,hestimate⟩

end Litex
