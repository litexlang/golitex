import Litex.Multivariable
universe u v w x y z
namespace Litex

theorem finiteComplexMagnitudeTriangle {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    Real.sqrt (∑ i, ‖f i + g i‖ ^ 2) ≤
      Real.sqrt (∑ i, ‖f i‖ ^ 2) + Real.sqrt (∑ i, ‖g i‖ ^ 2) := by
  simpa only [PiLp.norm_eq_of_L2,PiLp.add_apply,PiLp.toLp_apply] using
    norm_add_le (WithLp.toLp 2 f) (WithLp.toLp 2 g)

theorem euclideanNormFiniteSum {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) :
    denote p = M.number ((Real.sqrt (∑ i : Fin (NativeBridge.naturalValue (denote p.val.dimension)),
      ‖NativeBridge.complexValue (F.callValue (denote p.val.vector) (FiniteFunction.index i))‖ ^ 2) : ℝ) : ℂ) := by
  have sum := finiteSumMatrixIndex p.val.dimension p.wd.1
    (fun k => ((‖NativeBridge.complexValue (F.callValue (denote p.val.vector) k)‖ ^ 2 : ℝ) : ℂ))
  change sqrtValue (M.number (euclideanNormSum _ _)) = _
  rw [show euclideanNormSum (denote p.val.vector) p.val.dimension = _ from sum]
  let f := fun i : Fin (NativeBridge.naturalValue (denote p.val.dimension)) =>
    ‖NativeBridge.complexValue (F.callValue (denote p.val.vector) (FiniteFunction.index i))‖ ^ 2
  have casts : (∑ i, (f i : ℂ)) = ((∑ i, f i : ℝ) : ℂ) :=
    (map_sum Complex.ofRealHom f Finset.univ).symm
  rw [casts]
  exact sqrtValue_number _

theorem euclideanNormTriangleFromEntries {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hc : M.mem (denote c) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (entries : ∀ k, M.mem k (finiteSeqDomain n) →
      NativeBridge.complexValue (F.callValue (denote c) k) =
        NativeBridge.complexValue (F.callValue (denote a) k) +
          NativeBridge.complexValue (F.callValue (denote b) k)) :
    RealLeValue M (denote (euclideanNorm c n hn hc))
      (M.addValue (denote (euclideanNorm a n hn ha)) (denote (euclideanNorm b n hn hb))) := by
  rw [euclideanNormFiniteSum (euclideanNorm c n hn hc),
    euclideanNormFiniteSum (euclideanNorm a n hn ha),
    euclideanNormFiniteSum (euclideanNorm b n hn hb),M.add_numbers,← Complex.ofReal_add]
  apply (realLeValue_numbers _ _).mpr
  let f := fun i : Fin (NativeBridge.naturalValue (denote n)) =>
    NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.index i))
  let g := fun i : Fin (NativeBridge.naturalValue (denote n)) =>
    NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.index i))
  have sum : (∑ i : Fin (NativeBridge.naturalValue (denote n)),
      ‖NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.index i))‖ ^ 2) =
      ∑ i, ‖f i + g i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [entries _ ((F.sep_members _ _ _).mpr ⟨matrixIndexOfFin n hn i,True.intro⟩)]
  change Real.sqrt (∑ i : Fin (NativeBridge.naturalValue (denote n)),
      ‖NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.index i))‖ ^ 2) ≤
        Real.sqrt (∑ i, ‖f i‖ ^ 2) + Real.sqrt (∑ i, ‖g i‖ ^ 2)
  rw [sum]
  exact finiteComplexMagnitudeTriangle f g

theorem finiteNestedComplexMagnitudeTriangle {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f g : ι → κ → ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖f i j + g i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖f i j‖ ^ 2) + Real.sqrt (∑ i, ∑ j, ‖g i j‖ ^ 2) := by
  simpa only [Fintype.sum_prod_type] using
    finiteComplexMagnitudeTriangle (fun p : ι × κ => f p.1 p.2) (fun p => g p.1 p.2)

theorem frobeniusNormFiniteSum {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) :
    denote p = M.number ((Real.sqrt (∑ i : Fin (NativeBridge.naturalValue (denote p.val.rows)),
      ∑ j : Fin (NativeBridge.naturalValue (denote p.val.cols)),
        ‖NativeBridge.complexValue (F.callValue (denote p.val.matrix)
          (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)))‖ ^ 2) : ℝ) : ℂ) := by
  let f := fun (i : Fin (NativeBridge.naturalValue (denote p.val.rows)))
    (j : Fin (NativeBridge.naturalValue (denote p.val.cols))) =>
      ‖NativeBridge.complexValue (F.callValue (denote p.val.matrix)
        (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)))‖ ^ 2
  have sum : frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols =
      ∑ i, ∑ j, (f i j : ℂ) := by
    change (finiteAggregateValue false (matrixIndexValue p.val.rows) (fun r =>
      finiteAggregateValue false (matrixIndexValue p.val.cols) (fun c =>
        ((‖NativeBridge.complexValue (F.callValue (denote p.val.matrix)
          (FiniteFunction.pack2 r c))‖ ^ 2 : ℝ) : ℂ)))) = _
    rw [finiteSumMatrixIndex p.val.rows p.wd.1]
    apply Finset.sum_congr rfl
    intro i _
    exact finiteSumMatrixIndex p.val.cols p.wd.2.1 _
  have casts : (∑ i, ∑ j, (f i j : ℂ)) = ((∑ i, ∑ j, f i j : ℝ) : ℂ) := by
    calc
      _ = ∑ i, ((∑ j, f i j : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (map_sum Complex.ofRealHom (f i) Finset.univ).symm
      _ = _ := (map_sum Complex.ofRealHom (fun i => ∑ j, f i j) Finset.univ).symm
  change sqrtValue (M.number (frobeniusNormSum _ _ _)) = _
  rw [sum,casts]
  exact sqrtValue_number _

theorem frobeniusNormTriangleFromEntries {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y} {ε : Type z}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (m : Obj (M := M) δ) (n : Obj (M := M) ε) (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hc : M.mem (denote c) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (entries : ∀ i, M.mem i (matrixIndexValue m) → ∀ j, M.mem j (matrixIndexValue n) →
      NativeBridge.complexValue (F.callValue (denote c) (FiniteFunction.pack2 i j)) =
        NativeBridge.complexValue (F.callValue (denote a) (FiniteFunction.pack2 i j)) +
          NativeBridge.complexValue (F.callValue (denote b) (FiniteFunction.pack2 i j))) :
    RealLeValue M (denote (frobeniusNorm c m n hm hn hc))
      (M.addValue (denote (frobeniusNorm a m n hm hn ha)) (denote (frobeniusNorm b m n hm hn hb))) := by
  rw [frobeniusNormFiniteSum (frobeniusNorm c m n hm hn hc),
    frobeniusNormFiniteSum (frobeniusNorm a m n hm hn ha),
    frobeniusNormFiniteSum (frobeniusNorm b m n hm hn hb),M.add_numbers,← Complex.ofReal_add]
  apply (realLeValue_numbers _ _).mpr
  let f := fun (i : Fin (NativeBridge.naturalValue (denote m)))
    (j : Fin (NativeBridge.naturalValue (denote n))) =>
      NativeBridge.complexValue (F.callValue (denote a)
        (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)))
  let g := fun (i : Fin (NativeBridge.naturalValue (denote m)))
    (j : Fin (NativeBridge.naturalValue (denote n))) =>
      NativeBridge.complexValue (F.callValue (denote b)
        (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)))
  have sum : (∑ i : Fin (NativeBridge.naturalValue (denote m)),
      ∑ j : Fin (NativeBridge.naturalValue (denote n)),
        ‖NativeBridge.complexValue (F.callValue (denote c)
          (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)))‖ ^ 2) =
      ∑ i, ∑ j, ‖f i j + g i j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [entries _ (matrixIndexOfFin m hm i) _ (matrixIndexOfFin n hn j)]
  change Real.sqrt (∑ i : Fin (NativeBridge.naturalValue (denote m)),
      ∑ j : Fin (NativeBridge.naturalValue (denote n)),
        ‖NativeBridge.complexValue (F.callValue (denote c)
          (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)))‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖f i j‖ ^ 2) + Real.sqrt (∑ i, ∑ j, ‖g i j‖ ^ 2)
  rw [sum]
  exact finiteNestedComplexMagnitudeTriangle f g

theorem frobeniusNormTriangleEntrywise {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ))
    (hop : p.val.operation = .add) :
    RealLeValue M
      (denote (frobeniusNorm p p.val.rows p.val.cols p.wd.1 p.wd.2.1 (matrixEntrywiseInFnSet p)))
      (M.addValue
        (denote (frobeniusNorm p.val.left p.val.rows p.val.cols p.wd.1 p.wd.2.1 p.wd.2.2.1))
        (denote (frobeniusNorm p.val.right p.val.rows p.val.cols p.wd.1 p.wd.2.1 p.wd.2.2.2))) := by
  apply frobeniusNormTriangleFromEntries p.val.left p.val.right p p.val.rows p.val.cols
    p.wd.1 p.wd.2.1 p.wd.2.2.1 p.wd.2.2.2 (matrixEntrywiseInFnSet p)
  intro i hi j hj
  exact matrixAddEntryComplex p hop i j hi hj

theorem euclideanNormTriangleFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β))
    (g : Obj (M := M) (FormulaFn M)) (a : Obj (M := M) γ) (b : Obj (M := M) δ)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .complex)))
    (same : Same p.val.vector g)
    (domain : g.val.signature.domain = finiteSeqDomain p.val.dimension)
    (body : g.val.bodyValue = fun k =>
      M.addValue (M.mulValue (M.number 1) (F.callValue (denote a) k))
        (M.mulValue (M.number 1) (F.callValue (denote b) k))) :
    RealLeValue M (denote p)
      (M.addValue (denote (euclideanNorm a p.val.dimension p.wd.1 ha))
        (denote (euclideanNorm b p.val.dimension p.wd.1 hb))) := by
  apply euclideanNormTriangleFromEntries a b p.val.vector p.val.dimension p.wd.1 ha hb p.wd.2
  intro k hk
  change denote p.val.vector = denote g at same
  have call : F.callValue (denote p.val.vector) k =
      M.addValue (M.mulValue (M.number 1) (F.callValue (denote a) k))
        (M.mulValue (M.number 1) (F.callValue (denote b) k)) :=
    (congrArg (fun value => F.callValue value k) same).trans
      ((F.call_graphValue _ _ _ g.wd k (domain.symm ▸ hk)).trans (congrFun body k))
  obtain ⟨za,hza⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ ha hk)
  obtain ⟨zb,hzb⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ hb hk)
  rw [call,hza,hzb,M.mul_numbers,M.mul_numbers,one_mul,one_mul,M.add_numbers,
    NativeBridge.complexValue_number,NativeBridge.complexValue_number,NativeBridge.complexValue_number]

theorem euclideanNormTriangleNaturalFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β))
    (g : Obj (M := M) (FormulaFn M)) (a : Obj (M := M) γ) (b : Obj (M := M) δ)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .complex)))
    (same : Same p.val.vector g)
    (domain : g.val.signature.domain = finiteSeqDomain p.val.dimension)
    (body : g.val.bodyValue = fun k =>
      M.addValue (F.callValue (denote a) k) (F.callValue (denote b) k)) :
    RealLeValue M (denote p)
      (M.addValue (denote (euclideanNorm a p.val.dimension p.wd.1 ha))
        (denote (euclideanNorm b p.val.dimension p.wd.1 hb))) := by
  apply euclideanNormTriangleFromEntries a b p.val.vector p.val.dimension p.wd.1 ha hb p.wd.2
  intro k hk
  change denote p.val.vector = denote g at same
  have call : F.callValue (denote p.val.vector) k =
      M.addValue (F.callValue (denote a) k) (F.callValue (denote b) k) :=
    (congrArg (fun value => F.callValue value k) same).trans
      ((F.call_graphValue _ _ _ g.wd k (domain.symm ▸ hk)).trans (congrFun body k))
  obtain ⟨za,hza⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ ha hk)
  obtain ⟨zb,hzb⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ hb hk)
  rw [call,hza,hzb,M.add_numbers,NativeBridge.complexValue_number,
    NativeBridge.complexValue_number,NativeBridge.complexValue_number]

end Litex
