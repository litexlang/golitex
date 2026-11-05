import Litex.DifferentialAlgebraSupport

namespace Litex

theorem scalarDifferentialRemainderAddOfErrorBound
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b c : M.Value)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (first : ScalarDifferentialRemainderValue f point n a)
    (second : ScalarDifferentialRemainderValue g point n b)
    (errorBound : ∀ input, M.mem input (F.domainValue h) →
      RealLeValue M (scalarDifferentialErrorValue h point n c input)
        (M.addValue (scalarDifferentialErrorValue f point n a input)
          (scalarDifferentialErrorValue g point n b input))) :
    ScalarDifferentialRemainderValue h point n c := by
  intro epsilon hepsilon
  obtain ⟨_,e,he,hepos⟩ := (positiveReal_members _).mp hepsilon
  have halfPositive : 0 < e/2 := div_pos hepos (by norm_num)
  obtain ⟨deltaA,hdeltaA,controlA⟩ := first (M.number ((e/2 : ℝ) : ℂ))
    (numberInRPos (e/2) halfPositive)
  obtain ⟨deltaB,hdeltaB,controlB⟩ := second (M.number ((e/2 : ℝ) : ℂ))
    (numberInRPos (e/2) halfPositive)
  obtain ⟨_,da,hda,hdapos⟩ := (positiveReal_members _).mp hdeltaA
  obtain ⟨_,db,hdb,hdbpos⟩ := (positiveReal_members _).mp hdeltaB
  have radiusPositive := lt_min hdapos hdbpos
  let delta := semanticObject (M.number ((Min.min da db : ℝ) : ℂ))
    (M.member_isSet (numberInRPos (Min.min da db) radiusPositive))
  refine ⟨delta,numberInRPos (Min.min da db) radiusPositive,?_⟩
  intro input hinput positive near
  have positiveWitness := positive
  obtain ⟨_,distance,_,hd,_⟩ := positiveWitness
  change RealLtValue M (multivariableDistanceValue input point n)
    (M.number ((Min.min da db : ℝ) : ℂ)) at near
  rw [hd,realLtValue_numbers] at near
  have boundA := controlA input (hDf.symm ▸ hinput) positive
    ⟨distance,da,hd,hda,near.trans_le (min_le_left _ _)⟩
  have boundB := controlB input (hDg.symm ▸ hinput) positive
    ⟨distance,db,hd,hdb,near.trans_le (min_le_right _ _)⟩
  have witnessA := boundA
  have witnessB := boundB
  obtain ⟨ra,_,haeq,_,_⟩ := witnessA
  obtain ⟨rb,_,hbeq,_,_⟩ := witnessB
  have boundA' : ra < e/2*distance := (realLtValue_numbers _ _).mp (by
    simpa only [haeq,hd,M.mul_numbers,←Complex.ofReal_mul] using boundA)
  have boundB' : rb < e/2*distance := (realLtValue_numbers _ _).mp (by
    simpa only [hbeq,hd,M.mul_numbers,←Complex.ofReal_mul] using boundB)
  have comparison := errorBound input hinput
  rw [haeq,hbeq,M.add_numbers,←Complex.ofReal_add] at comparison
  obtain ⟨rc,rhs,hceq,hrhs,order⟩ := comparison
  have rhsEq : rhs = ra+rb := (Complex.ofReal_injective (M.number_injective hrhs)).symm
  have order' : rc ≤ ra+rb := rhsEq ▸ order
  refine ⟨rc,e*distance,hceq,?_,?_⟩
  · rw [he,hd,M.mul_numbers,←Complex.ofReal_mul]
  · nlinarith

theorem scalarDifferentialErrorAddOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b c input : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (ha : M.mem a (realMatrixSetValue (M.number 1) n))
    (hb : M.mem b (realMatrixSetValue (M.number 1) n))
    (hc : M.mem c (realMatrixSetValue (M.number 1) n))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      F.callValue h x = M.addValue (F.callValue f x) (F.callValue g x))
    (entries : ∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 (M.number 1) k)) =
        NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 (M.number 1) k)) +
          NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 (M.number 1) k)))
    (hinput : M.mem input (F.domainValue h)) :
    RealLeValue M (scalarDifferentialErrorValue h point n c input)
      (M.addValue (scalarDifferentialErrorValue f point n a input)
        (scalarDifferentialErrorValue g point n b input)) := by
  have inputVector : M.mem input (realVectorSetValue n) := by
    obtain ⟨signature,member,inputs,_⟩ := hh
    exact inputs input ((F.domainValue_eq signature.domain_isSet member) ▸ hinput)
  let difference := multivariableDifferenceValue input point n
  have differenceVector : M.mem difference (realVectorSetValue n) :=
    F.graph_inFnSet _ _ _ (fun k hk => subValuesInReal
      (F.call_mem _ _ _ _ inputVector hk) (F.call_mem _ _ _ _ hp hk))
  have oneNatural : M.mem (M.number 1) (M.standard .natural) := by
    exact (M.natural_members _).mpr ⟨1,by norm_num⟩
  have oneIndex : M.mem (M.number 1) (closedRangeValue (M.number 1) (M.number 1)) := by
    simpa only [Int.cast_one] using
      (closedRangeValue_members (M := M) 1 1 (M.number 1)).mpr
        ⟨1,by norm_num,le_rfl,le_rfl⟩
  have linear := matrixApplyValueAddFromComplexEntries a b c difference (M.number 1) n
    (M.number 1) oneNatural hn ha hb hc differenceVector oneIndex entries
  obtain ⟨fx,hfx⟩ := (M.real_members _).mp
    (multivariableFunctionReturnsReal f n input hf (hDf.symm ▸ hinput))
  obtain ⟨fp,hfp⟩ := (M.real_members _).mp
    (multivariableFunctionReturnsReal f n point hf (hDf.symm ▸ hpoint))
  obtain ⟨gx,hgx⟩ := (M.real_members _).mp
    (multivariableFunctionReturnsReal g n input hg (hDg.symm ▸ hinput))
  obtain ⟨gp,hgp⟩ := (M.real_members _).mp
    (multivariableFunctionReturnsReal g n point hg (hDg.symm ▸ hpoint))
  obtain ⟨pa,hpa⟩ := (M.real_members _).mp (F.call_mem _ _ _ _
    (matrixApplyValueInVector a difference (M.number 1) n oneNatural hn ha differenceVector)
    ((F.sep_members _ _ _).mpr ⟨oneIndex,True.intro⟩))
  obtain ⟨pb,hpb⟩ := (M.real_members _).mp (F.call_mem _ _ _ _
    (matrixApplyValueInVector b difference (M.number 1) n oneNatural hn hb differenceVector)
    ((F.sep_members _ _ _).mpr ⟨oneIndex,True.intro⟩))
  dsimp only [difference] at linear hpa hpb
  have firstError : scalarDifferentialErrorValue f point n a input =
      M.number ((|fx-fp-pa| : ℝ) : ℂ) := by
    simp only [scalarDifferentialErrorValue,hfx,hfp,hpa,
      M.sub_numbers,←Complex.ofReal_sub,absValue_number]
  have secondError : scalarDifferentialErrorValue g point n b input =
      M.number ((|gx-gp-pb| : ℝ) : ℂ) := by
    simp only [scalarDifferentialErrorValue,hgx,hgp,hpb,
      M.sub_numbers,←Complex.ofReal_sub,absValue_number]
  have totalError : scalarDifferentialErrorValue h point n c input =
      M.number ((|(fx-fp-pa)+(gx-gp-pb)| : ℝ) : ℂ) := by
    simp only [scalarDifferentialErrorValue,formula input hinput,
      formula point hpoint,linear,hfx,hfp,hgx,hgp,hpa,hpb,
      M.add_numbers,M.sub_numbers,←Complex.ofReal_add,←Complex.ofReal_sub,absValue_number]
    have identity : fx+gx-(fp+gp)-(pa+pb) = (fx-fp-pa)+(gx-gp-pb) := by ring
    rw [identity]
  rw [totalError,firstError,secondError,M.add_numbers,←Complex.ofReal_add,
    realLeValue_numbers]
  exact abs_add_le _ _

theorem scalarDifferentialAtAddOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b c : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (hc : M.mem c (realMatrixSetValue (M.number 1) n))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      F.callValue h x = M.addValue (F.callValue f x) (F.callValue g x))
    (entries : ∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 (M.number 1) k)) =
        NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 (M.number 1) k)) +
          NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 (M.number 1) k)))
    (first : HasScalarDifferentialAtValue M f point n a)
    (second : HasScalarDifferentialAtValue M g point n b) :
    HasScalarDifferentialAtValue M h point n c := by
  refine ⟨hc,hDf ▸ first.2.1,?_⟩
  apply scalarDifferentialRemainderAddOfErrorBound f g h point n a b c hDf hDg
    first.2.2 second.2.2
  intro input hinput
  exact scalarDifferentialErrorAddOfEntries f g h point n a b c input hn hp hf hg hh
    hDf hDg hpoint first.1 second.1 hc formula entries hinput

theorem scalarDifferentialErrorSubtractOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b c input : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (ha : M.mem a (realMatrixSetValue (M.number 1) n))
    (hb : M.mem b (realMatrixSetValue (M.number 1) n))
    (hc : M.mem c (realMatrixSetValue (M.number 1) n))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      F.callValue h x = M.subValue (F.callValue f x) (F.callValue g x))
    (entries : ∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 (M.number 1) k)) =
        NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 (M.number 1) k)) -
          NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 (M.number 1) k)))
    (hinput : M.mem input (F.domainValue h)) :
    RealLeValue M (scalarDifferentialErrorValue h point n c input)
      (M.addValue (scalarDifferentialErrorValue f point n a input)
        (scalarDifferentialErrorValue g point n b input)) := by
  have inputVector : M.mem input (realVectorSetValue n) := by
    obtain ⟨signature,member,inputs,_⟩ := hh
    exact inputs input ((F.domainValue_eq signature.domain_isSet member) ▸ hinput)
  let difference := multivariableDifferenceValue input point n
  have differenceVector : M.mem difference (realVectorSetValue n) :=
    F.graph_inFnSet _ _ _ (fun k hk => subValuesInReal
      (F.call_mem _ _ _ _ inputVector hk) (F.call_mem _ _ _ _ hp hk))
  have oneNatural : M.mem (M.number 1) (M.standard .natural) := by
    exact (M.natural_members _).mpr ⟨1,by norm_num⟩
  have oneIndex : M.mem (M.number 1) (closedRangeValue (M.number 1) (M.number 1)) := by
    simpa only [Int.cast_one] using
      (closedRangeValue_members (M := M) 1 1 (M.number 1)).mpr
        ⟨1,by norm_num,le_rfl,le_rfl⟩
  have linear := matrixApplyValueLinearCombinationFromComplexEntries a b c difference
    (M.number 1) n (M.number 1) 1 (-1) oneNatural hn ha hb hc differenceVector oneIndex
    (fun k hk => by rw [entries k hk]; ring)
  obtain ⟨fx,hfx⟩ := (M.real_members _).mp
    (multivariableFunctionReturnsReal f n input hf (hDf.symm ▸ hinput))
  obtain ⟨fp,hfp⟩ := (M.real_members _).mp
    (multivariableFunctionReturnsReal f n point hf (hDf.symm ▸ hpoint))
  obtain ⟨gx,hgx⟩ := (M.real_members _).mp
    (multivariableFunctionReturnsReal g n input hg (hDg.symm ▸ hinput))
  obtain ⟨gp,hgp⟩ := (M.real_members _).mp
    (multivariableFunctionReturnsReal g n point hg (hDg.symm ▸ hpoint))
  obtain ⟨pa,hpa⟩ := (M.real_members _).mp (F.call_mem _ _ _ _
    (matrixApplyValueInVector a difference (M.number 1) n oneNatural hn ha differenceVector)
    ((F.sep_members _ _ _).mpr ⟨oneIndex,True.intro⟩))
  obtain ⟨pb,hpb⟩ := (M.real_members _).mp (F.call_mem _ _ _ _
    (matrixApplyValueInVector b difference (M.number 1) n oneNatural hn hb differenceVector)
    ((F.sep_members _ _ _).mpr ⟨oneIndex,True.intro⟩))
  dsimp only [difference] at linear hpa hpb
  have firstError : scalarDifferentialErrorValue f point n a input =
      M.number ((|fx-fp-pa| : ℝ) : ℂ) := by
    simp only [scalarDifferentialErrorValue,hfx,hfp,hpa,
      M.sub_numbers,←Complex.ofReal_sub,absValue_number]
  have secondError : scalarDifferentialErrorValue g point n b input =
      M.number ((|gx-gp-pb| : ℝ) : ℂ) := by
    simp only [scalarDifferentialErrorValue,hgx,hgp,hpb,
      M.sub_numbers,←Complex.ofReal_sub,absValue_number]
  have totalError : scalarDifferentialErrorValue h point n c input =
      M.number ((|(fx-fp-pa)-(gx-gp-pb)| : ℝ) : ℂ) := by
    simp only [scalarDifferentialErrorValue,formula input hinput,
      formula point hpoint,linear,hfx,hfp,hgx,hgp,hpa,hpb,
      M.mul_numbers,M.add_numbers,M.sub_numbers,one_mul,neg_one_mul,
      ←Complex.ofReal_neg,←Complex.ofReal_add,←Complex.ofReal_sub,absValue_number]
    have identity : fx-gx-(fp-gp)-(pa + -pb) = (fx-fp-pa)-(gx-gp-pb) := by ring
    rw [identity]
  rw [totalError,firstError,secondError,M.add_numbers,←Complex.ofReal_add,
    realLeValue_numbers]
  simpa only [sub_zero,zero_sub,abs_neg] using
    (abs_sub_le (fx-fp-pa) 0 (gx-gp-pb))

theorem scalarDifferentialAtSubtractOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n a b c : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M h n)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (hc : M.mem c (realMatrixSetValue (M.number 1) n))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      F.callValue h x = M.subValue (F.callValue f x) (F.callValue g x))
    (entries : ∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 (M.number 1) k)) =
        NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 (M.number 1) k)) -
          NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 (M.number 1) k)))
    (first : HasScalarDifferentialAtValue M f point n a)
    (second : HasScalarDifferentialAtValue M g point n b) :
    HasScalarDifferentialAtValue M h point n c := by
  refine ⟨hc,hDf ▸ first.2.1,?_⟩
  apply scalarDifferentialRemainderAddOfErrorBound f g h point n a b c hDf hDg
    first.2.2 second.2.2
  intro input hinput
  exact scalarDifferentialErrorSubtractOfEntries f g h point n a b c input hn hp hf hg hh
    hDf hDg hpoint first.1 second.1 hc formula entries hinput

end Litex
