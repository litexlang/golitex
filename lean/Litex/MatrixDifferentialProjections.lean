import Litex.Multivariable

universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

noncomputable def differentialMatrixDiagonalValue (a n : M.Value) : M.Value :=
  F.graphValue (F.sepValue (closedRangeValue (M.number 1) n) (fun _ => True))
    (M.standard .real) (fun k => F.callValue a (FiniteFunction.pack2 k k))

theorem differentialMatrixDiagonalEntryReal (a n k : M.Value)
    (ha : M.mem a (realMatrixSetValue n n))
    (hk : M.mem k (closedRangeValue (M.number 1) n)) :
    M.mem (F.callValue a (FiniteFunction.pack2 k k)) (M.standard .real) := by
  apply F.call_mem _ _ _ _ ha
  apply (F.sep_members _ _ _).mpr
  exact ⟨(FiniteFunction.cart2_members _ _ _).mpr ⟨k,hk,k,hk,rfl⟩,True.intro⟩

theorem differentialMatrixDiagonalMember (a n : M.Value)
    (ha : M.mem a (realMatrixSetValue n n)) :
    M.mem (differentialMatrixDiagonalValue a n) (realVectorSetValue n) := by
  apply F.graph_inFnSet
  intro k hk
  exact differentialMatrixDiagonalEntryReal a n k ha ((F.sep_members _ _ _).mp hk).1

theorem differentialMatrixDiagonalCall (a n k : M.Value)
    (ha : M.mem a (realMatrixSetValue n n))
    (hk : M.mem k (closedRangeValue (M.number 1) n)) :
    F.callValue (differentialMatrixDiagonalValue a n) k=F.callValue a (FiniteFunction.pack2 k k) := by
  apply F.call_graphValue _ _ _
    (fun k hk => differentialMatrixDiagonalEntryReal a n k ha ((F.sep_members _ _ _).mp hk).1)
  exact (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩

theorem differentialMatrixDiagonalSum (a n : M.Value)
    (ha : M.mem a (realMatrixSetValue n n)) :
    vectorSumValue (differentialMatrixDiagonalValue a n) n=M.number (matrixTraceRawValue a n) := by
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro k hk
  rw [differentialMatrixDiagonalCall a n k ha hk]

theorem differentialMatrixTraceReal (a n : M.Value)
    (hn : M.mem n (M.standard .natural))
    (ha : M.mem a (realMatrixSetValue n n)) :
    M.mem (M.number (matrixTraceRawValue a n)) (M.standard .real) := by
  let dimension := semanticObject n (M.member_isSet hn)
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite dimension hn)
  intro k hk
  have realEntry := differentialMatrixDiagonalEntryReal a n k ha hk
  rw [←NativeBridge.complexValue_spec _ (M.real_subset_complex _ realEntry)]
  exact realEntry

theorem divergenceOfJacobianMatrix (f point n matrix : M.Value)
    (hn : M.mem n (M.standard .natural))
    (h : HasJacobianAtValue M f point n n matrix) :
    HasDivergenceAtValue M f point n (M.number (matrixTraceRawValue matrix n)) := by
  have member := differentialMatrixDiagonalMember matrix n h.1
  let diagonal := semanticObject (differentialMatrixDiagonalValue matrix n) (M.member_isSet member)
  refine ⟨differentialMatrixTraceReal matrix n hn h.1,diagonal,member,?_,
    differentialMatrixDiagonalSum matrix n h.1⟩
  intro k hk
  change HasPartialDerivativeAtValue M _ point n k
    (F.callValue (differentialMatrixDiagonalValue matrix n) k)
  rw [differentialMatrixDiagonalCall matrix n k h.1 hk]
  exact h.2 k hk k hk

theorem laplacianOfHessianMatrix (f point n matrix : M.Value)
    (hn : M.mem n (M.standard .natural))
    (h : HasHessianAtValue M f point n matrix) :
    HasLaplacianAtValue M f point n (M.number (matrixTraceRawValue matrix n)) := by
  have member := differentialMatrixDiagonalMember matrix n h.1
  let diagonal := semanticObject (differentialMatrixDiagonalValue matrix n) (M.member_isSet member)
  refine ⟨differentialMatrixTraceReal matrix n hn h.1,diagonal,member,?_,
    differentialMatrixDiagonalSum matrix n h.1⟩
  intro k hk
  change HasSecondPartialAtValue M f point n k k
    (F.callValue (differentialMatrixDiagonalValue matrix n) k)
  rw [differentialMatrixDiagonalCall matrix n k h.1 hk]
  exact h.2 k hk k hk

theorem rawTupleInRealVector {n : ℕ} (values : Fin n → M.Value)
    (realValues : ∀ i, M.mem (values i) (M.standard .real)) :
    M.mem (FiniteFunction.tupleValue values) (realVectorSetValue (M.number (n : ℂ))) := by
  let t := tuple values (fun i => M.member_isSet (realValues i))
  let signature := FunctionSignature.ofDomain (finiteSeqDomain (number (M := M) (n : ℂ)))
    (M.standard .real) (finiteSeqDomain_isSet _) (M.standard_isSet .real)
  exact tupleInFunctionSet t signature (finiteSeqDomain_number n) realValues

theorem curlOfJacobianEntries (f point matrix value : M.Value)
    (h : HasJacobianAtValue M f point (M.number 3) (M.number 3) matrix)
    (hv : M.mem value (realVectorSetValue (M.number 3)))
    (e1 : F.callValue value (M.number 1)=M.subValue
      (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 2)))
      (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 3))))
    (e2 : F.callValue value (M.number 2)=M.subValue
      (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 3)))
      (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 1))))
    (e3 : F.callValue value (M.number 3)=M.subValue
      (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 1)))
      (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 2)))) :
    HasCurlAtValue M f point value := by
  have indexMember (k : ℤ) (lo : 1≤k) (hi : k≤3) :
      M.mem (M.number (k : ℂ)) (closedRangeValue (M.number 1) (M.number 3)) := by
    simpa only [Int.cast_one,Int.cast_ofNat] using
      (closedRangeValue_members (M := M) 1 3 _).mpr ⟨k,rfl,lo,hi⟩
  have i1 : M.mem (M.number 1) (closedRangeValue (M.number 1) (M.number 3)) := by
    simpa only [Int.cast_one,Int.cast_ofNat] using indexMember 1 (by omega) (by omega)
  have i2 : M.mem (M.number 2) (closedRangeValue (M.number 1) (M.number 3)) := by
    simpa only [Int.cast_one,Int.cast_ofNat] using indexMember 2 (by omega) (by omega)
  have i3 : M.mem (M.number 3) (closedRangeValue (M.number 1) (M.number 3)) := by
    simpa only [Int.cast_one,Int.cast_ofNat] using indexMember 3 (by omega) (by omega)
  let rows : Fin 6 → M.Value := ![M.number 3,M.number 2,M.number 1,M.number 3,M.number 2,M.number 1]
  let cols : Fin 6 → M.Value := ![M.number 2,M.number 3,M.number 3,M.number 1,M.number 1,M.number 2]
  let values : Fin 6 → M.Value := fun i => F.callValue matrix (FiniteFunction.pack2 (rows i) (cols i))
  have realValues (i : Fin 6) : M.mem (values i) (M.standard .real) := by
    apply F.call_mem _ _ _ _ h.1
    apply (F.sep_members _ _ _).mpr
    refine ⟨(FiniteFunction.cart2_members _ _ _).mpr ⟨rows i,?_,cols i,?_,rfl⟩,True.intro⟩
    · fin_cases i <;> dsimp [rows,cols] <;> first | exact i1 | exact i2 | exact i3
    · fin_cases i <;> dsimp [rows,cols] <;> first | exact i1 | exact i2 | exact i3
  let partials := semanticObject (FiniteFunction.tupleValue values) (FiniteFunction.tuple_isSet values)
  have p1 : F.callValue (denote partials) (M.number 1)=
      F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 2)) := by
    simpa [partials,semanticObject_denote,values,rows,cols,FiniteFunction.index] using
      (FiniteFunction.call_tuple values (0 : Fin 6))
  have p2 : F.callValue (denote partials) (M.number 2)=
      F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 3)) := by
    simpa [partials,semanticObject_denote,values,rows,cols,FiniteFunction.index] using
      (FiniteFunction.call_tuple values (1 : Fin 6))
  have p3 : F.callValue (denote partials) (M.number 3)=
      F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 3)) := by
    simpa [partials,semanticObject_denote,values,rows,cols,FiniteFunction.index] using
      (FiniteFunction.call_tuple values (2 : Fin 6))
  have p4 : F.callValue (denote partials) (M.number 4)=
      F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 1)) := by
    simpa [partials,semanticObject_denote,values,rows,cols,FiniteFunction.index] using
      (FiniteFunction.call_tuple values (3 : Fin 6))
  have p5 : F.callValue (denote partials) (M.number 5)=
      F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 1)) := by
    simpa [partials,semanticObject_denote,values,rows,cols,FiniteFunction.index] using
      (FiniteFunction.call_tuple values (4 : Fin 6))
  have p6 : F.callValue (denote partials) (M.number 6)=
      F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 2)) := by
    simpa [partials,semanticObject_denote,values,rows,cols,FiniteFunction.index] using
      (FiniteFunction.call_tuple values (5 : Fin 6))
  refine ⟨hv,partials,rawTupleInRealVector values realValues,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [p1] using h.2 (M.number 3) i3 (M.number 2) i2
  · simpa only [p2] using h.2 (M.number 2) i2 (M.number 3) i3
  · simpa only [p3] using h.2 (M.number 1) i1 (M.number 3) i3
  · simpa only [p4] using h.2 (M.number 3) i3 (M.number 1) i1
  · simpa only [p5] using h.2 (M.number 2) i2 (M.number 1) i1
  · simpa only [p6] using h.2 (M.number 1) i1 (M.number 2) i2
  · simpa only [p1,p2] using e1
  · simpa only [p3,p4] using e2
  · simpa only [p5,p6] using e3

def jacobianCurlVectorValue (matrix : M.Value) : M.Value :=
  FiniteFunction.tupleValue ![
    M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 2)))
      (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 3))),
    M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 3)))
      (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 1))),
    M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 1)))
      (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 2)))]

theorem jacobianCurlVectorReal (matrix : M.Value)
    (hm : M.mem matrix (realMatrixSetValue (M.number 3) (M.number 3))) :
    M.mem (jacobianCurlVectorValue matrix) (realVectorSetValue (M.number 3)) := by
  have indexMember (k : ℤ) (lo : 1≤k) (hi : k≤3) :
      M.mem (M.number (k : ℂ)) (closedRangeValue (M.number 1) (M.number 3)) := by
    simpa only [Int.cast_one,Int.cast_ofNat] using
      (closedRangeValue_members (M := M) 1 3 _).mpr ⟨k,rfl,lo,hi⟩
  have i1 : M.mem (M.number 1) (closedRangeValue (M.number 1) (M.number 3)) := by
    simpa only [Int.cast_one,Int.cast_ofNat] using indexMember 1 (by omega) (by omega)
  have i2 : M.mem (M.number 2) (closedRangeValue (M.number 1) (M.number 3)) := by
    simpa only [Int.cast_one,Int.cast_ofNat] using indexMember 2 (by omega) (by omega)
  have i3 : M.mem (M.number 3) (closedRangeValue (M.number 1) (M.number 3)) := by
    simpa only [Int.cast_one,Int.cast_ofNat] using indexMember 3 (by omega) (by omega)
  have entry (i j : M.Value)
      (hi : M.mem i (closedRangeValue (M.number 1) (M.number 3)))
      (hj : M.mem j (closedRangeValue (M.number 1) (M.number 3))) :
      M.mem (F.callValue matrix (FiniteFunction.pack2 i j)) (M.standard .real) := by
    apply F.call_mem _ _ _ _ hm
    exact (F.sep_members _ _ _).mpr
      ⟨(FiniteFunction.cart2_members _ _ _).mpr ⟨i,hi,j,hj,rfl⟩,True.intro⟩
  apply rawTupleInRealVector
  intro i
  fin_cases i
  · exact subValuesInReal (entry _ _ i3 i2) (entry _ _ i2 i3)
  · exact subValuesInReal (entry _ _ i1 i3) (entry _ _ i3 i1)
  · exact subValuesInReal (entry _ _ i2 i1) (entry _ _ i1 i2)

theorem curlOfJacobianMatrix (f point matrix : M.Value)
    (h : HasJacobianAtValue M f point (M.number 3) (M.number 3) matrix) :
    HasCurlAtValue M f point (jacobianCurlVectorValue matrix) := by
  apply curlOfJacobianEntries f point matrix _ h (jacobianCurlVectorReal matrix h.1)
  · simpa [jacobianCurlVectorValue,FiniteFunction.index] using
      (FiniteFunction.call_tuple (M := M) ![
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 2)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 3))),
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 3)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 1))),
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 1)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 2)))] (0 : Fin 3))
  · simpa [jacobianCurlVectorValue,FiniteFunction.index] using
      (FiniteFunction.call_tuple (M := M) ![
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 2)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 3))),
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 3)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 1))),
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 1)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 2)))] (1 : Fin 3))
  · simpa [jacobianCurlVectorValue,FiniteFunction.index] using
      (FiniteFunction.call_tuple (M := M) ![
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 2)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 3))),
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 3)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 3) (M.number 1))),
        M.subValue (F.callValue matrix (FiniteFunction.pack2 (M.number 2) (M.number 1)))
          (F.callValue matrix (FiniteFunction.pack2 (M.number 1) (M.number 2)))] (2 : Fin 3))
end Litex

