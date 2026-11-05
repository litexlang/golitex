import Litex.BuiltinNormTriangle

namespace Litex

theorem matrixApplyValueAddFromComplexEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b c vector m n row : M.Value)
    (hm : M.mem m (M.standard .natural))
    (hn : M.mem n (M.standard .natural))
    (ha : M.mem a (realMatrixSetValue m n))
    (hb : M.mem b (realMatrixSetValue m n))
    (hc : M.mem c (realMatrixSetValue m n))
    (hv : M.mem vector (realVectorSetValue n))
    (hr : M.mem row (closedRangeValue (M.number 1) m))
    (entries : ∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 row k)) =
        NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) +
          NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 row k))) :
    F.callValue (matrixApplyValue c vector m n) row =
      M.addValue (F.callValue (matrixApplyValue a vector m n) row)
        (F.callValue (matrixApplyValue b vector m n) row) := by
  rw [matrixApplyValueRow c vector m n row (M.member_isSet hm) (M.member_isSet hn) hc hv hr,
    matrixApplyValueRow a vector m n row (M.member_isSet hm) (M.member_isSet hn) ha hv hr,
    matrixApplyValueRow b vector m n row (M.member_isSet hm) (M.member_isSet hn) hb hv hr,
    M.add_numbers]
  apply congrArg M.number
  trans finiteAggregateValue false (closedRangeValue (M.number 1) n) (fun k =>
    NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) *
        NativeBridge.complexValue (F.callValue vector k) +
      NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 row k)) *
        NativeBridge.complexValue (F.callValue vector k))
  · apply finiteAggregateValue_congr
    intro k hk
    rw [entries k hk, add_mul]
  · exact finiteSumValueAdd _ _ _
      (matrixIndexFinite (semanticObject n (M.member_isSet hn)) hn)

theorem matrixApplyValueLinearCombinationFromComplexEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b c vector m n row : M.Value) (z w : ℂ)
    (hm : M.mem m (M.standard .natural))
    (hn : M.mem n (M.standard .natural))
    (ha : M.mem a (realMatrixSetValue m n))
    (hb : M.mem b (realMatrixSetValue m n))
    (hc : M.mem c (realMatrixSetValue m n))
    (hv : M.mem vector (realVectorSetValue n))
    (hr : M.mem row (closedRangeValue (M.number 1) m))
    (entries : ∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 row k)) =
        z * NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) +
          w * NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 row k))) :
    F.callValue (matrixApplyValue c vector m n) row =
      M.addValue (M.mulValue (M.number z) (F.callValue (matrixApplyValue a vector m n) row))
        (M.mulValue (M.number w) (F.callValue (matrixApplyValue b vector m n) row)) := by
  rw [matrixApplyValueRow c vector m n row (M.member_isSet hm) (M.member_isSet hn) hc hv hr,
    matrixApplyValueRow a vector m n row (M.member_isSet hm) (M.member_isSet hn) ha hv hr,
    matrixApplyValueRow b vector m n row (M.member_isSet hm) (M.member_isSet hn) hb hv hr,
    M.mul_numbers, M.mul_numbers, M.add_numbers]
  apply congrArg M.number
  have finite : (memberSet (closedRangeValue (M.number 1) n)).Finite :=
    matrixIndexFinite (semanticObject n (M.member_isSet hn)) hn
  trans finiteAggregateValue false (closedRangeValue (M.number 1) n) (fun k =>
    z * (NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) *
        NativeBridge.complexValue (F.callValue vector k)) +
      w * (NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 row k)) *
        NativeBridge.complexValue (F.callValue vector k)))
  · apply finiteAggregateValue_congr
    intro k hk
    rw [entries k hk]
    ring
  · rw [finiteSumValueAdd _ _ _ finite,
      finiteSumValueMulLeft _ _ _ finite, finiteSumValueMulLeft _ _ _ finite]

theorem complexRemainderAddOfMembers
    {M : Semantics.{u}} (x y x0 y0 a b : M.Value)
    (hx : M.mem x (M.standard .complex)) (hy : M.mem y (M.standard .complex))
    (hx0 : M.mem x0 (M.standard .complex)) (hy0 : M.mem y0 (M.standard .complex))
    (ha : M.mem a (M.standard .complex)) (hb : M.mem b (M.standard .complex)) :
    NativeBridge.complexValue (M.subValue
      (M.subValue (M.addValue x y) (M.addValue x0 y0)) (M.addValue a b)) =
      NativeBridge.complexValue (M.subValue (M.subValue x x0) a) +
        NativeBridge.complexValue (M.subValue (M.subValue y y0) b) := by
  obtain ⟨x,rfl⟩ := (M.complex_members _).mp hx
  obtain ⟨y,rfl⟩ := (M.complex_members _).mp hy
  obtain ⟨x0,rfl⟩ := (M.complex_members _).mp hx0
  obtain ⟨y0,rfl⟩ := (M.complex_members _).mp hy0
  obtain ⟨a,rfl⟩ := (M.complex_members _).mp ha
  obtain ⟨b,rfl⟩ := (M.complex_members _).mp hb
  simp only [M.add_numbers,M.sub_numbers,NativeBridge.complexValue_number]
  ring

theorem complexRemainderSubtractOfMembers
    {M : Semantics.{u}} (x y x0 y0 a b : M.Value)
    (hx : M.mem x (M.standard .complex)) (hy : M.mem y (M.standard .complex))
    (hx0 : M.mem x0 (M.standard .complex)) (hy0 : M.mem y0 (M.standard .complex))
    (ha : M.mem a (M.standard .complex)) (hb : M.mem b (M.standard .complex)) :
    NativeBridge.complexValue (M.subValue
      (M.subValue (M.subValue x y) (M.subValue x0 y0)) (M.subValue a b)) =
      NativeBridge.complexValue (M.subValue (M.subValue x x0) a) -
        NativeBridge.complexValue (M.subValue (M.subValue y y0) b) := by
  obtain ⟨x,rfl⟩ := (M.complex_members _).mp hx
  obtain ⟨y,rfl⟩ := (M.complex_members _).mp hy
  obtain ⟨x0,rfl⟩ := (M.complex_members _).mp hx0
  obtain ⟨y0,rfl⟩ := (M.complex_members _).mp hy0
  obtain ⟨a,rfl⟩ := (M.complex_members _).mp ha
  obtain ⟨b,rfl⟩ := (M.complex_members _).mp hb
  simp only [M.sub_numbers,NativeBridge.complexValue_number]
  ring

theorem matrixApplyValueSubtractFromComplexEntries
    {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b c vector m n row : M.Value)
    (hm : M.mem m (M.standard .natural))
    (hn : M.mem n (M.standard .natural))
    (ha : M.mem a (realMatrixSetValue m n))
    (hb : M.mem b (realMatrixSetValue m n))
    (hc : M.mem c (realMatrixSetValue m n))
    (hv : M.mem vector (realVectorSetValue n))
    (hr : M.mem row (closedRangeValue (M.number 1) m))
    (entries : ∀ k, M.mem k (closedRangeValue (M.number 1) n) →
      NativeBridge.complexValue (F.callValue c (FiniteFunction.pack2 row k)) =
        NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 row k)) -
          NativeBridge.complexValue (F.callValue b (FiniteFunction.pack2 row k))) :
    F.callValue (matrixApplyValue c vector m n) row =
      M.subValue (F.callValue (matrixApplyValue a vector m n) row)
        (F.callValue (matrixApplyValue b vector m n) row) := by
  have linear := matrixApplyValueLinearCombinationFromComplexEntries a b c vector m n row
    1 (-1) hm hn ha hb hc hv hr (fun k hk => by rw [entries k hk]; ring)
  obtain ⟨ra,hra⟩ := (M.real_members _).mp (F.call_mem _ _ _ _
    (matrixApplyValueInVector a vector m n hm hn ha hv)
    ((F.sep_members _ _ _).mpr ⟨hr,True.intro⟩))
  obtain ⟨rb,hrb⟩ := (M.real_members _).mp (F.call_mem _ _ _ _
    (matrixApplyValueInVector b vector m n hm hn hb hv)
    ((F.sep_members _ _ _).mpr ⟨hr,True.intro⟩))
  refine linear.trans ?_
  rw [hra,hrb,M.mul_numbers,M.mul_numbers,M.add_numbers,M.sub_numbers]
  congr 1
  ring

theorem finiteComplexMagnitudeDifference {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    Real.sqrt (∑ i, ‖f i - g i‖ ^ 2) ≤
      Real.sqrt (∑ i, ‖f i‖ ^ 2) + Real.sqrt (∑ i, ‖g i‖ ^ 2) := by
  simpa only [PiLp.norm_eq_of_L2,PiLp.sub_apply,PiLp.toLp_apply] using
    norm_sub_le (WithLp.toLp 2 f) (WithLp.toLp 2 g)

theorem euclideanNormDifferenceFromEntries {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hc : M.mem (denote c) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (entries : ∀ k, M.mem k (finiteSeqDomain n) →
      NativeBridge.complexValue (F.callValue (denote c) k) =
        NativeBridge.complexValue (F.callValue (denote a) k) -
          NativeBridge.complexValue (F.callValue (denote b) k)) :
    RealLeValue M (denote (euclideanNorm c n hn hc))
      (M.addValue (denote (euclideanNorm a n hn ha)) (denote (euclideanNorm b n hn hb))) := by
  rw [euclideanNormFiniteSum (euclideanNorm c n hn hc),
    euclideanNormFiniteSum (euclideanNorm a n hn ha),
    euclideanNormFiniteSum (euclideanNorm b n hn hb),M.add_numbers,←Complex.ofReal_add]
  apply (realLeValue_numbers _ _).mpr
  let f := fun i : Fin (NativeBridge.naturalValue (denote n)) =>
    NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.index i))
  let g := fun i : Fin (NativeBridge.naturalValue (denote n)) =>
    NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.index i))
  have sum : (∑ i : Fin (NativeBridge.naturalValue (denote n)),
      ‖NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.index i))‖ ^ 2) =
      ∑ i, ‖f i - g i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [entries _ ((F.sep_members _ _ _).mpr ⟨matrixIndexOfFin n hn i,True.intro⟩)]
  change Real.sqrt (∑ i : Fin (NativeBridge.naturalValue (denote n)),
      ‖NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.index i))‖ ^ 2) ≤
        Real.sqrt (∑ i, ‖f i‖ ^ 2) + Real.sqrt (∑ i, ‖g i‖ ^ 2)
  rw [sum]
  exact finiteComplexMagnitudeDifference f g

theorem complexValueAddOfMembers {M : Semantics.{u}} (x y : M.Value)
    (hx : M.mem x (M.standard .complex)) (hy : M.mem y (M.standard .complex)) :
    NativeBridge.complexValue (M.addValue x y) =
      NativeBridge.complexValue x + NativeBridge.complexValue y := by
  obtain ⟨a,rfl⟩ := (M.complex_members _).mp hx
  obtain ⟨b,rfl⟩ := (M.complex_members _).mp hy
  rw [M.add_numbers,NativeBridge.complexValue_number,
    NativeBridge.complexValue_number,NativeBridge.complexValue_number]

theorem complexValueSubtractOfMembers {M : Semantics.{u}} (x y : M.Value)
    (hx : M.mem x (M.standard .complex)) (hy : M.mem y (M.standard .complex)) :
    NativeBridge.complexValue (M.subValue x y) =
      NativeBridge.complexValue x - NativeBridge.complexValue y := by
  obtain ⟨a,rfl⟩ := (M.complex_members _).mp hx
  obtain ⟨b,rfl⟩ := (M.complex_members _).mp hy
  rw [M.sub_numbers,NativeBridge.complexValue_number,
    NativeBridge.complexValue_number,NativeBridge.complexValue_number]

end Litex
