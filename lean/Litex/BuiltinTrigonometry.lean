import Litex.ElementaryFunctions
universe u v w
namespace Litex

theorem sineLowerBoundValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SinObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number ((-1 : ℝ) : ℂ)) : Le bound p := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.leOfDenoteReal bound p (-1) (Real.sin r) hb (denoteSin p r hr)
    (Real.neg_one_le_sin r)

theorem sineUpperBoundValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SinObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number ((1 : ℝ) : ℂ)) : Le p bound := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.leOfDenoteReal p bound (Real.sin r) 1 (denoteSin p r hr) hb
    (Real.sin_le_one r)

theorem cosineLowerBoundValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (CosObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number ((-1 : ℝ) : ℂ)) : Le bound p := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.leOfDenoteReal bound p (-1) (Real.cos r) hb (denoteCos p r hr)
    (Real.neg_one_le_cos r)

theorem cosineUpperBoundValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (CosObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number ((1 : ℝ) : ℂ)) : Le p bound := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.leOfDenoteReal p bound (Real.cos r) 1 (denoteCos p r hr) hb
    (Real.cos_le_one r)

theorem cosineNonzeroOnPrincipalInterval {M : Semantics.{u}} {α : Type v}
    [Representation M α] (p : Obj (M := M) (CosObj (M := M) α))
    (hlo : Lt (number (((-(Real.pi / 2)) : ℝ) : ℂ)) p.val.arg)
    (hhi : Lt p.val.arg (number (((Real.pi / 2) : ℝ) : ℂ))) : ¬ Same p (number 0) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  have lo := (NativeBridge.lt_iff_ofDenoteReal _ _ (-(Real.pi / 2)) r rfl hr).mp hlo
  have hi := (NativeBridge.lt_iff_ofDenoteReal _ _ r (Real.pi / 2) hr rfl).mp hhi
  intro hzero
  apply ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨lo, hi⟩)
  exact Complex.ofReal_injective (M.number_injective ((denoteCos p r hr).symm.trans hzero))

theorem sineNonzeroOnPrincipalInterval {M : Semantics.{u}} {α : Type v}
    [Representation M α] (p : Obj (M := M) (SinObj (M := M) α))
    (hlo : Lt (number 0) p.val.arg)
    (hhi : Lt p.val.arg (number ((Real.pi : ℝ) : ℂ))) : ¬ Same p (number 0) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  have lo := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 r rfl hr).mp hlo
  have hi := (NativeBridge.lt_iff_ofDenoteReal _ _ r Real.pi hr rfl).mp hhi
  intro hzero
  apply ne_of_gt (Real.sin_pos_of_pos_of_lt_pi lo hi)
  exact Complex.ofReal_injective (M.number_injective ((denoteSin p r hr).symm.trans hzero))

theorem arcsineSinePrincipalValue {M : Semantics.{u}} {α : Type v}
    [Representation M α] (p : Obj (M := M) (ArcsinObj (M := M) (SinObj (M := M) α)))
    (hlo : Le (number (((-(Real.pi / 2)) : ℝ) : ℂ)) p.val.arg.val.arg)
    (hhi : Le p.val.arg.val.arg (number (((Real.pi / 2) : ℝ) : ℂ))) :
    Same p p.val.arg.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.val.arg.wd
  have lo := (NativeBridge.le_iff_ofDenoteReal _ _ (-(Real.pi / 2)) r rfl hr).mp hlo
  have hi := (NativeBridge.le_iff_ofDenoteReal _ _ r (Real.pi / 2) hr rfl).mp hhi
  change denote p = denote p.val.arg.val.arg
  rw [denoteArcsin p (Real.sin r) (denoteSin p.val.arg r hr), Real.arcsin_sin lo hi, hr]

theorem arccosineCosinePrincipalValue {M : Semantics.{u}} {α : Type v}
    [Representation M α] (p : Obj (M := M) (ArccosObj (M := M) (CosObj (M := M) α)))
    (hlo : Le (number 0) p.val.arg.val.arg)
    (hhi : Le p.val.arg.val.arg (number ((Real.pi : ℝ) : ℂ))) :
    Same p p.val.arg.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.val.arg.wd
  have lo := (NativeBridge.le_iff_ofDenoteReal _ _ 0 r rfl hr).mp hlo
  have hi := (NativeBridge.le_iff_ofDenoteReal _ _ r Real.pi hr rfl).mp hhi
  change denote p = denote p.val.arg.val.arg
  rw [denoteArccos p (Real.cos r) (denoteCos p.val.arg r hr), Real.arccos_cos lo hi, hr]

theorem arctangentTangentPrincipalValue {M : Semantics.{u}} {α : Type v}
    [Representation M α] (p : Obj (M := M) (ArctanObj (M := M) (TanObj (M := M) α)))
    (hlo : Lt (number (((-(Real.pi / 2)) : ℝ) : ℂ)) p.val.arg.val.arg)
    (hhi : Lt p.val.arg.val.arg (number (((Real.pi / 2) : ℝ) : ℂ))) :
    Same p p.val.arg.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.val.arg.wd.1
  have lo := (NativeBridge.lt_iff_ofDenoteReal _ _ (-(Real.pi / 2)) r rfl hr).mp hlo
  have hi := (NativeBridge.lt_iff_ofDenoteReal _ _ r (Real.pi / 2) hr rfl).mp hhi
  change denote p = denote p.val.arg.val.arg
  rw [denoteArctan p (Real.tan r) (denoteTan p.val.arg r hr), Real.arctan_tan lo hi, hr]

theorem arccotangentCotangentPrincipalValue {M : Semantics.{u}} {α : Type v}
    [Representation M α] (p : Obj (M := M) (ArccotObj (M := M) (CotObj (M := M) α)))
    (hlo : Lt (number 0) p.val.arg.val.arg)
    (hhi : Lt p.val.arg.val.arg (number ((Real.pi : ℝ) : ℂ))) :
    Same p p.val.arg.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.val.arg.wd.1
  have lo := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 r rfl hr).mp hlo
  have hi := (NativeBridge.lt_iff_ofDenoteReal _ _ r Real.pi hr rfl).mp hhi
  have hlo' : -(Real.pi / 2) < Real.pi / 2 - r := by linarith
  have hhi' : Real.pi / 2 - r < Real.pi / 2 := by linarith
  have hinverse : nativeArccot (nativeCot r) = r := by
    rw [nativeArccot, nativeCot]
    have hc : Real.cos r / Real.sin r = Real.tan (Real.pi / 2 - r) := by
      rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
    rw [hc, Real.arctan_tan hlo' hhi']
    ring
  change denote p = denote p.val.arg.val.arg
  rw [denoteArccot p (nativeCot r) (denoteCot p.val.arg r hr), hinverse, hr]


theorem arcsineFromKnownSineValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArcsinObj (M := M) α))
    (s : Obj (M := M) (SinObj (M := M) β))
    (hlo : Le (number (((-(Real.pi / 2)) : ℝ) : ℂ)) s.val.arg)
    (hhi : Le s.val.arg (number (((Real.pi / 2) : ℝ) : ℂ)))
    (heq : Same p.val.arg s) : Same p s.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp s.wd
  have lo := (NativeBridge.le_iff_ofDenoteReal _ _ (-(Real.pi / 2)) r rfl hr).mp hlo
  have hi := (NativeBridge.le_iff_ofDenoteReal _ _ r (Real.pi / 2) hr rfl).mp hhi
  change denote p = denote s.val.arg
  rw [denoteArcsin p (Real.sin r) (heq.trans (denoteSin s r hr)), Real.arcsin_sin lo hi, hr]



theorem arcsinePrincipalLowerValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArcsinObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number (((-(Real.pi / 2)) : ℝ) : ℂ)) : Le bound p := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd.1
  exact NativeBridge.leOfDenoteReal bound p (-(Real.pi / 2)) (Real.arcsin r) hb (denoteArcsin p r hr)
    (Real.neg_pi_div_two_le_arcsin r)

theorem arcsinePrincipalUpperValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArcsinObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number (((Real.pi / 2) : ℝ) : ℂ)) : Le p bound := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd.1
  exact NativeBridge.leOfDenoteReal p bound (Real.arcsin r) (Real.pi / 2) (denoteArcsin p r hr) hb
    (Real.arcsin_le_pi_div_two r)

theorem arccosinePrincipalLowerValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArccosObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number (((0) : ℝ) : ℂ)) : Le bound p := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd.1
  exact NativeBridge.leOfDenoteReal bound p (0) (Real.arccos r) hb (denoteArccos p r hr)
    (Real.arccos_nonneg r)

theorem arccosinePrincipalUpperValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArccosObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number (((Real.pi) : ℝ) : ℂ)) : Le p bound := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd.1
  exact NativeBridge.leOfDenoteReal p bound (Real.arccos r) (Real.pi) (denoteArccos p r hr) hb
    (Real.arccos_le_pi r)

theorem arctangentPrincipalLowerValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArctanObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number (((-(Real.pi / 2)) : ℝ) : ℂ)) : Lt bound p := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.ltOfDenoteReal bound p (-(Real.pi / 2)) (Real.arctan r) hb (denoteArctan p r hr)
    (Real.neg_pi_div_two_lt_arctan r)

theorem arctangentPrincipalUpperValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArctanObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number (((Real.pi / 2) : ℝ) : ℂ)) : Lt p bound := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.ltOfDenoteReal p bound (Real.arctan r) (Real.pi / 2) (denoteArctan p r hr) hb
    (Real.arctan_lt_pi_div_two r)

theorem arccotangentPrincipalLowerValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArccotObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number (((0) : ℝ) : ℂ)) : Lt bound p := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.ltOfDenoteReal bound p (0) (Litex.nativeArccot r) hb (denoteArccot p r hr)
    (by dsimp [Litex.nativeArccot]; linarith [Real.neg_pi_div_two_lt_arctan r, Real.arctan_lt_pi_div_two r])

theorem arccotangentPrincipalUpperValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ArccotObj (M := M) α)) (bound : Obj (M := M) β)
    (hb : denote bound = M.number (((Real.pi) : ℝ) : ℂ)) : Lt p bound := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.ltOfDenoteReal p bound (Litex.nativeArccot r) (Real.pi) (denoteArccot p r hr) hb
    (by dsimp [Litex.nativeArccot]; linarith [Real.neg_pi_div_two_lt_arctan r, Real.arctan_lt_pi_div_two r])


end Litex
