import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_subsets_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : Litex.Subset (Litex.NPos (M := M)) (Litex.QPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.NPos (M := M)) (Litex.QPos (M := M)) (fun _a _ha => (Litex.inQPos_intro _a (Litex.naturalToRational _a (Litex.inNPos_natural _a _ha)) (Litex.inNPos_positive _a _ha))))
      )
  )

theorem h_5 : Litex.Subset (Litex.QPos (M := M)) (Litex.RPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.QPos (M := M)) (Litex.RPos (M := M)) (fun _a _ha => (Litex.inRPos_intro _a (Litex.rationalToReal _a (Litex.inQPos_base _a _ha)) (Litex.inQPos_positive _a _ha))))
      )
  )

theorem h_13 : Litex.Subset (Litex.ZNeg (M := M)) (Litex.QNeg (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.ZNeg (M := M)) (Litex.QNeg (M := M)) (fun _a _ha => (Litex.inQNeg_intro _a (Litex.integerToRational _a (Litex.inZNeg_base _a _ha)) (Litex.inZNeg_negative _a _ha))))
      )
  )

theorem h_25 : Litex.Subset (Litex.QNeg (M := M)) (Litex.RNeg (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.QNeg (M := M)) (Litex.RNeg (M := M)) (fun _a _ha => (Litex.inRNeg_intro _a (Litex.rationalToReal _a (Litex.inQNeg_base _a _ha)) (Litex.inQNeg_negative _a _ha))))
      )
  )

theorem h_41 : Litex.Subset (Litex.QPos (M := M)) (Litex.QStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.QPos (M := M)) (Litex.QStar (M := M)) (fun _a _ha => (Litex.inQStar_intro _a (Litex.inQPos_base _a _ha) (fun h => (Litex.ltNotSame (Litex.number (M := M) 0) _a (Litex.inQPos_positive _a _ha)) h.symm))))
      )
  )

theorem h_65 : Litex.Subset (Litex.RNeg (M := M)) (Litex.RStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.RNeg (M := M)) (Litex.RStar (M := M)) (fun _a _ha => (Litex.inRStar_intro _a (Litex.inRNeg_base _a _ha) (Litex.ltNotSame _a (Litex.number (M := M) 0) (Litex.inRNeg_negative _a _ha)))))
      )
  )

theorem h_89 : Litex.Subset (Litex.ZStar (M := M)) (Litex.QStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.ZStar (M := M)) (Litex.QStar (M := M)) (fun _a _ha => (Litex.inQStar_intro _a (Litex.integerToRational _a (Litex.inZStar_base _a _ha)) (Litex.inZStar_nonzero _a _ha))))
      )
  )

theorem h_117 : Litex.Subset (Litex.QStar (M := M)) (Litex.RStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.QStar (M := M)) (Litex.RStar (M := M)) (fun _a _ha => (Litex.inRStar_intro _a (Litex.rationalToReal _a (Litex.inQStar_base _a _ha)) (Litex.inQStar_nonzero _a _ha))))
      )
  )

theorem h_149 : Litex.Subset (Litex.RStar (M := M)) (Litex.CStar (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.RStar (M := M)) (Litex.CStar (M := M)) (fun _a _ha => (Litex.inCStar_intro _a (Litex.realToComplex _a (Litex.inRStar_base _a _ha)) (Litex.inRStar_nonzero _a _ha))))
      )
  )

theorem h_185 : Litex.Subset (Litex.CStar (M := M)) (Litex.C (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.subsetOfForall (Litex.CStar (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.inCStar_base _a _ha)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_subsets_x2f_statement_x2e_lit
