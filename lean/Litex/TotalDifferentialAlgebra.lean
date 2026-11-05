import Litex.DifferentialAlgebraSupport

namespace Litex

theorem totalDifferentialRemainderAddOfErrorBound
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c : M.Value)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (first : TotalDifferentialRemainderValue f point n m a)
    (second : TotalDifferentialRemainderValue g point n m b)
    (errorBound : ∀ input, M.mem input (F.domainValue h) →
      RealLeValue M (totalDifferentialErrorValue h point n m c input)
        (M.addValue (totalDifferentialErrorValue f point n m a input)
          (totalDifferentialErrorValue g point n m b input))) :
    TotalDifferentialRemainderValue h point n m c := by
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

theorem totalDifferentialRemainderVectorInRealVector
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m matrix input : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hpoint : M.mem point (F.domainValue f))
    (hinput : M.mem input (F.domainValue f))
    (hA : M.mem matrix (realMatrixSetValue m n)) :
    M.mem (totalDifferentialRemainderVectorValue f point n m matrix input)
      (realVectorSetValue m) := by
  have inputOutput := multivariableVectorFunctionReturns f n m input hf hinput
  have pointOutput := multivariableVectorFunctionReturns f n m point hf hpoint
  have inputVector : M.mem input (realVectorSetValue n) := by
    obtain ⟨signature,member,inputs,_⟩ := hf
    exact inputs input ((F.domainValue_eq signature.domain_isSet member) ▸ hinput)
  have differenceVector : M.mem (multivariableDifferenceValue input point n)
      (realVectorSetValue n) :=
    F.graph_inFnSet _ _ _ (fun k hk => subValuesInReal
      (F.call_mem _ _ _ _ inputVector hk) (F.call_mem _ _ _ _ hp hk))
  have applied := matrixApplyValueInVector matrix
    (multivariableDifferenceValue input point n) m n hm hn hA differenceVector
  exact F.graph_inFnSet _ _ _ (fun row hrow => subValuesInReal
    (subValuesInReal (F.call_mem _ _ _ _ inputOutput hrow)
      (F.call_mem _ _ _ _ pointOutput hrow))
    (F.call_mem _ _ _ _ applied hrow))

theorem totalDifferentialErrorTriangleOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c input : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (hinput : M.mem input (F.domainValue h))
    (ha : M.mem a (realMatrixSetValue m n))
    (hb : M.mem b (realMatrixSetValue m n))
    (hc : M.mem c (realMatrixSetValue m n))
    (entries : ∀ row, M.mem row (closedRangeValue (M.number 1) m) →
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue h point n m c input) row) =
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue f point n m a input) row) +
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue g point n m b input) row)) :
    RealLeValue M (totalDifferentialErrorValue h point n m c input)
      (M.addValue (totalDifferentialErrorValue f point n m a input)
        (totalDifferentialErrorValue g point n m b input)) := by
  have validA := totalDifferentialRemainderVectorInRealVector f point n m a input hn hm
    hp hf (hDf.symm ▸ hpoint) (hDf.symm ▸ hinput) ha
  have validB := totalDifferentialRemainderVectorInRealVector g point n m b input hn hm
    hp hg (hDg.symm ▸ hpoint) (hDg.symm ▸ hinput) hb
  have validC := totalDifferentialRemainderVectorInRealVector h point n m c input hn hm
    hp hh hpoint hinput hc
  let left := semanticObject (totalDifferentialRemainderVectorValue f point n m a input)
    (M.member_isSet validA)
  let right := semanticObject (totalDifferentialRemainderVectorValue g point n m b input)
    (M.member_isSet validB)
  let sum := semanticObject (totalDifferentialRemainderVectorValue h point n m c input)
    (M.member_isSet validC)
  let rows := semanticObject m (M.member_isSet hm)
  have rowsNatural : In rows N := hm
  have triangle := euclideanNormTriangleFromEntries left right sum rows rowsNatural
    (functionRealToComplex validA) (functionRealToComplex validB)
    (functionRealToComplex validC)
    (fun row hrow => entries row ((F.sep_members _ _ _).mp hrow).1)
  exact triangle

theorem totalDifferentialRemainderVectorCall
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m matrix input row : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hpoint : M.mem point (F.domainValue f))
    (hinput : M.mem input (F.domainValue f))
    (hA : M.mem matrix (realMatrixSetValue m n))
    (hrow : M.mem row (closedRangeValue (M.number 1) m)) :
    F.callValue (totalDifferentialRemainderVectorValue f point n m matrix input) row =
      M.subValue (M.subValue (F.callValue (F.callValue f input) row)
        (F.callValue (F.callValue f point) row))
        (F.callValue (matrixApplyValue matrix (multivariableDifferenceValue input point n) m n) row) := by
  have inputOutput := multivariableVectorFunctionReturns f n m input hf hinput
  have pointOutput := multivariableVectorFunctionReturns f n m point hf hpoint
  have inputVector : M.mem input (realVectorSetValue n) := by
    obtain ⟨signature,member,inputs,_⟩ := hf
    exact inputs input ((F.domainValue_eq signature.domain_isSet member) ▸ hinput)
  have differenceVector : M.mem (multivariableDifferenceValue input point n)
      (realVectorSetValue n) :=
    F.graph_inFnSet _ _ _ (fun k hk => subValuesInReal
      (F.call_mem _ _ _ _ inputVector hk) (F.call_mem _ _ _ _ hp hk))
  have applied := matrixApplyValueInVector matrix
    (multivariableDifferenceValue input point n) m n hm hn hA differenceVector
  exact F.call_graphValue _ _ _ (fun j hj => subValuesInReal
    (subValuesInReal (F.call_mem _ _ _ _ inputOutput hj)
      (F.call_mem _ _ _ _ pointOutput hj))
    (F.call_mem _ _ _ _ applied hj)) row ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩)

theorem totalDifferentialRemainderEntryAddOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c input row : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (hinput : M.mem input (F.domainValue h))
    (ha : M.mem a (realMatrixSetValue m n))
    (hb : M.mem b (realMatrixSetValue m n))
    (hc : M.mem c (realMatrixSetValue m n))
    (hrow : M.mem row (closedRangeValue (M.number 1) m))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      ∀ i, M.mem i (closedRangeValue (M.number 1) m) →
        F.callValue (F.callValue h x) i =
          M.addValue (F.callValue (F.callValue f x) i) (F.callValue (F.callValue g x) i))
    (entries : ∀ i, M.mem i (closedRangeValue (M.number 1) m) →
      ∀ j, M.mem j (closedRangeValue (M.number 1) n) →
        NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 i j)) =
          NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 i j)) +
            NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 i j))) :
    NativeBridge.complexValue (F.callValue
      (totalDifferentialRemainderVectorValue h point n m c input) row) =
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue f point n m a input) row) +
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue g point n m b input) row) := by
  have inputVector : M.mem input (realVectorSetValue n) := by
    obtain ⟨signature,member,inputs,_⟩ := hh
    exact inputs input ((F.domainValue_eq signature.domain_isSet member) ▸ hinput)
  have differenceVector : M.mem (multivariableDifferenceValue input point n)
      (realVectorSetValue n) :=
    F.graph_inFnSet _ _ _ (fun k hk => subValuesInReal
      (F.call_mem _ _ _ _ inputVector hk) (F.call_mem _ _ _ _ hp hk))
  have linear := matrixApplyValueAddFromComplexEntries a b c
    (multivariableDifferenceValue input point n) m n row hm hn ha hb hc
    differenceVector hrow (fun j hj => entries row hrow j hj)
  rw [totalDifferentialRemainderVectorCall h point n m c input row hn hm hp hh hpoint hinput hc hrow,
    totalDifferentialRemainderVectorCall f point n m a input row hn hm hp hf
      (hDf.symm ▸ hpoint) (hDf.symm ▸ hinput) ha hrow,
    totalDifferentialRemainderVectorCall g point n m b input row hn hm hp hg
      (hDg.symm ▸ hpoint) (hDg.symm ▸ hinput) hb hrow,
    formula input hinput row hrow,formula point hpoint row hrow,linear]
  apply complexRemainderAddOfMembers
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns f n m input hf (hDf.symm ▸ hinput))
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns g n m input hg (hDg.symm ▸ hinput))
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns f n m point hf (hDf.symm ▸ hpoint))
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns g n m point hg (hDg.symm ▸ hpoint))
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (matrixApplyValueInVector a _ m n hm hn ha differenceVector)
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (matrixApplyValueInVector b _ m n hm hn hb differenceVector)
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))

theorem totalDifferentialAtAddOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (hc : M.mem c (realMatrixSetValue m n))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      ∀ i, M.mem i (closedRangeValue (M.number 1) m) →
        F.callValue (F.callValue h x) i =
          M.addValue (F.callValue (F.callValue f x) i) (F.callValue (F.callValue g x) i))
    (entries : ∀ i, M.mem i (closedRangeValue (M.number 1) m) →
      ∀ j, M.mem j (closedRangeValue (M.number 1) n) →
        NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 i j)) =
          NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 i j)) +
            NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 i j)))
    (first : HasTotalDifferentialAtValue M f point n m a)
    (second : HasTotalDifferentialAtValue M g point n m b) :
    HasTotalDifferentialAtValue M h point n m c := by
  refine ⟨hc,hDf ▸ first.2.1,?_⟩
  apply totalDifferentialRemainderAddOfErrorBound f g h point n m a b c hDf hDg
    first.2.2 second.2.2
  intro input hinput
  apply totalDifferentialErrorTriangleOfEntries f g h point n m a b c input hn hm hp
    hf hg hh hDf hDg hpoint hinput first.1 second.1 hc
  intro row hrow
  exact totalDifferentialRemainderEntryAddOfEntries f g h point n m a b c input row
    hn hm hp hf hg hh hDf hDg hpoint hinput first.1 second.1 hc hrow formula entries

theorem totalDifferentialErrorDifferenceOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c input : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (hinput : M.mem input (F.domainValue h))
    (ha : M.mem a (realMatrixSetValue m n))
    (hb : M.mem b (realMatrixSetValue m n))
    (hc : M.mem c (realMatrixSetValue m n))
    (entries : ∀ row, M.mem row (closedRangeValue (M.number 1) m) →
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue h point n m c input) row) =
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue f point n m a input) row) -
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue g point n m b input) row)) :
    RealLeValue M (totalDifferentialErrorValue h point n m c input)
      (M.addValue (totalDifferentialErrorValue f point n m a input)
        (totalDifferentialErrorValue g point n m b input)) := by
  have validA := totalDifferentialRemainderVectorInRealVector f point n m a input hn hm
    hp hf (hDf.symm ▸ hpoint) (hDf.symm ▸ hinput) ha
  have validB := totalDifferentialRemainderVectorInRealVector g point n m b input hn hm
    hp hg (hDg.symm ▸ hpoint) (hDg.symm ▸ hinput) hb
  have validC := totalDifferentialRemainderVectorInRealVector h point n m c input hn hm
    hp hh hpoint hinput hc
  let left := semanticObject (totalDifferentialRemainderVectorValue f point n m a input)
    (M.member_isSet validA)
  let right := semanticObject (totalDifferentialRemainderVectorValue g point n m b input)
    (M.member_isSet validB)
  let sum := semanticObject (totalDifferentialRemainderVectorValue h point n m c input)
    (M.member_isSet validC)
  let rows := semanticObject m (M.member_isSet hm)
  have rowsNatural : In rows N := hm
  have triangle := euclideanNormDifferenceFromEntries left right sum rows rowsNatural
    (functionRealToComplex validA) (functionRealToComplex validB)
    (functionRealToComplex validC)
    (fun row hrow => entries row ((F.sep_members _ _ _).mp hrow).1)
  exact triangle

theorem totalDifferentialRemainderEntrySubtractOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c input row : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (hinput : M.mem input (F.domainValue h))
    (ha : M.mem a (realMatrixSetValue m n))
    (hb : M.mem b (realMatrixSetValue m n))
    (hc : M.mem c (realMatrixSetValue m n))
    (hrow : M.mem row (closedRangeValue (M.number 1) m))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      ∀ i, M.mem i (closedRangeValue (M.number 1) m) →
        F.callValue (F.callValue h x) i =
          M.subValue (F.callValue (F.callValue f x) i) (F.callValue (F.callValue g x) i))
    (entries : ∀ i, M.mem i (closedRangeValue (M.number 1) m) →
      ∀ j, M.mem j (closedRangeValue (M.number 1) n) →
        NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 i j)) =
          NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 i j)) -
            NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 i j))) :
    NativeBridge.complexValue (F.callValue
      (totalDifferentialRemainderVectorValue h point n m c input) row) =
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue f point n m a input) row) -
      NativeBridge.complexValue (F.callValue
        (totalDifferentialRemainderVectorValue g point n m b input) row) := by
  have inputVector : M.mem input (realVectorSetValue n) := by
    obtain ⟨signature,member,inputs,_⟩ := hh
    exact inputs input ((F.domainValue_eq signature.domain_isSet member) ▸ hinput)
  have differenceVector : M.mem (multivariableDifferenceValue input point n)
      (realVectorSetValue n) :=
    F.graph_inFnSet _ _ _ (fun k hk => subValuesInReal
      (F.call_mem _ _ _ _ inputVector hk) (F.call_mem _ _ _ _ hp hk))
  have linear := matrixApplyValueSubtractFromComplexEntries a b c
    (multivariableDifferenceValue input point n) m n row hm hn ha hb hc
    differenceVector hrow (fun j hj => entries row hrow j hj)
  rw [totalDifferentialRemainderVectorCall h point n m c input row hn hm hp hh hpoint hinput hc hrow,
    totalDifferentialRemainderVectorCall f point n m a input row hn hm hp hf
      (hDf.symm ▸ hpoint) (hDf.symm ▸ hinput) ha hrow,
    totalDifferentialRemainderVectorCall g point n m b input row hn hm hp hg
      (hDg.symm ▸ hpoint) (hDg.symm ▸ hinput) hb hrow,
    formula input hinput row hrow,formula point hpoint row hrow,linear]
  apply complexRemainderSubtractOfMembers
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns f n m input hf (hDf.symm ▸ hinput))
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns g n m input hg (hDg.symm ▸ hinput))
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns f n m point hf (hDf.symm ▸ hpoint))
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns g n m point hg (hDg.symm ▸ hpoint))
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (matrixApplyValueInVector a _ m n hm hn ha differenceVector)
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))
  · exact M.real_subset_complex _ (F.call_mem _ _ _ _
      (matrixApplyValueInVector b _ m n hm hn hb differenceVector)
      ((F.sep_members _ _ _).mpr ⟨hrow,True.intro⟩))

theorem totalDifferentialAtSubtractOfEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hm : M.mem m (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (hDf : F.domainValue f = F.domainValue h)
    (hDg : F.domainValue g = F.domainValue h)
    (hpoint : M.mem point (F.domainValue h))
    (hc : M.mem c (realMatrixSetValue m n))
    (formula : ∀ x, M.mem x (F.domainValue h) →
      ∀ i, M.mem i (closedRangeValue (M.number 1) m) →
        F.callValue (F.callValue h x) i =
          M.subValue (F.callValue (F.callValue f x) i) (F.callValue (F.callValue g x) i))
    (entries : ∀ i, M.mem i (closedRangeValue (M.number 1) m) →
      ∀ j, M.mem j (closedRangeValue (M.number 1) n) →
        NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 i j)) =
          NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 i j)) -
            NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 i j)))
    (first : HasTotalDifferentialAtValue M f point n m a)
    (second : HasTotalDifferentialAtValue M g point n m b) :
    HasTotalDifferentialAtValue M h point n m c := by
  refine ⟨hc,hDf ▸ first.2.1,?_⟩
  apply totalDifferentialRemainderAddOfErrorBound f g h point n m a b c hDf hDg
    first.2.2 second.2.2
  intro input hinput
  apply totalDifferentialErrorDifferenceOfEntries f g h point n m a b c input hn hm hp
    hf hg hh hDf hDg hpoint hinput first.1 second.1 hc
  intro row hrow
  exact totalDifferentialRemainderEntrySubtractOfEntries f g h point n m a b c input row
    hn hm hp hf hg hh hDf hDg hpoint hinput first.1 second.1 hc hrow formula entries

end Litex
