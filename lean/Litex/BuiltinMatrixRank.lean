import Litex.Multivariable
universe u v w x y z
namespace Litex

theorem matrixRankProductBounds {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y} {ε : Type z}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (m : Obj (M := M) γ) (k : Obj (M := M) δ) (n : Obj (M := M) ε)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k n) (M.standard .complex))) :
    RealLeValue M (matrixRankValue (denote (matrixMultiply a b m k n hm hk hn ha hb)) (denote m) (denote n))
      (matrixRankValue (denote a) (denote m) (denote k)) ∧
    RealLeValue M (matrixRankValue (denote (matrixMultiply a b m k n hm hk hn ha hb)) (denote m) (denote n))
      (matrixRankValue (denote b) (denote k) (denote n)) := by
  let A := matrixComplexValue (denote a) m k
  let B := matrixComplexValue (denote b) k n
  have product : matrixRankValue (denote (matrixMultiply a b m k n hm hk hn ha hb)) (denote m) (denote n) =
      M.number (((A*B).rank : ℝ) : ℂ) := by
    change M.number ((matrixComplexValue (denote (matrixMultiply a b m k n hm hk hn ha hb)) m n).rank : ℂ) = _
    rw [matrixComplexValueMultiply]
    simp only [Complex.ofReal_natCast]
    rfl
  constructor
  · refine ⟨((A*B).rank : ℝ),(A.rank : ℝ),product,?_,?_⟩
    · change M.number (A.rank : ℂ) = _
      simp only [Complex.ofReal_natCast]
    · exact_mod_cast Matrix.rank_mul_le_left A B
  · refine ⟨((A*B).rank : ℝ),(B.rank : ℝ),product,?_,?_⟩
    · change M.number (B.rank : ℂ) = _
      simp only [Complex.ofReal_natCast]
    · exact_mod_cast Matrix.rank_mul_le_right A B

end Litex
