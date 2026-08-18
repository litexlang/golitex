/-
The same point-only axiom hierarchy and first derived theorems as `main.lit`,
expressed in pure Lean 4. Relations use functions into `Prop` because Prelude
does not provide the first-class relation-set notation used by Litex.

The structures are explicit assumption bundles, not claims that a model of
the axioms has been constructed. This is handwritten comparison code, not
compiler output.
-/

namespace TarskiGeometryFromAxiomsSameMathInLean

abbrev Betweenness (Point : Type) := Point → Point → Point → Prop

abbrev SegmentCongruence (Point : Type) :=
  Point → Point → Point → Point → Prop

def Collinear {Point : Type} (Bet : Betweenness Point)
    (a b c : Point) : Prop :=
  Bet a b c ∨ Bet b c a ∨ Bet c a b

def IsMidpoint {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point) (midpoint endpointA endpointB : Point) :
    Prop :=
  Bet endpointA midpoint endpointB ∧
    Cong endpointA midpoint midpoint endpointB

structure TarskiNeutralDimensionless (Point : Type) where
  Bet : Betweenness Point
  Cong : SegmentCongruence Point
  congrPseudoReflexivity : ∀ p1 p2, Cong p1 p2 p2 p1
  congrInnerTransitivity : ∀ p1 p2 p3 p4 p5 p6,
    Cong p1 p2 p3 p4 → Cong p1 p2 p5 p6 → Cong p3 p4 p5 p6
  congrIdentity : ∀ p1 p2 p3, Cong p1 p2 p3 p3 → p1 = p2
  segmentConstruction : ∀ p1 p2 p3 p4,
    ∃ x, Bet p1 p2 x ∧ Cong p2 x p3 p4
  fiveSegment : ∀ p1 p2 p3 p4 p5 p6 p7 p8,
    Cong p1 p3 p2 p4 →
    Cong p3 p5 p4 p6 →
    Cong p1 p7 p2 p8 →
    Cong p3 p7 p4 p8 →
    Bet p1 p3 p5 →
    Bet p2 p4 p6 →
    p1 ≠ p3 →
    Cong p5 p7 p6 p8
  betweenIdentity : ∀ p1 p2, Bet p1 p2 p1 → p1 = p2
  innerPasch : ∀ p1 p2 p3 p4 p5,
    Bet p1 p4 p3 → Bet p2 p5 p3 →
      ∃ x, Bet p4 x p2 ∧ Bet p5 x p1
  lowerA : Point
  lowerB : Point
  lowerC : Point
  lowerDimension1 : ¬ Bet lowerA lowerB lowerC
  lowerDimension2 : ¬ Bet lowerB lowerC lowerA
  lowerDimension3 : ¬ Bet lowerC lowerA lowerB

theorem segment_congruence_reflexive {Point : Type}
    (G : TarskiNeutralDimensionless Point) (a b : Point) :
    G.Cong a b a b :=
  G.congrInnerTransitivity b a a b a b
    (G.congrPseudoReflexivity b a)
    (G.congrPseudoReflexivity b a)

theorem segment_congruence_symmetric {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c d : Point}
    (h : G.Cong a b c d) : G.Cong c d a b :=
  G.congrInnerTransitivity a b c d a b h
    (segment_congruence_reflexive G a b)

theorem midpoint_is_between {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point) {midpoint endpointA endpointB : Point}
    (h : IsMidpoint Bet Cong midpoint endpointA endpointB) :
    Bet endpointA midpoint endpointB :=
  h.1

structure TarskiNeutralWithDecidableEquality (Point : Type) where
  neutral : TarskiNeutralDimensionless Point
  pointEqualityDecidable : ∀ p1 p2 : Point, p1 = p2 ∨ p1 ≠ p2

structure Tarski2D (Point : Type) where
  base : TarskiNeutralWithDecidableEquality Point
  upperDimension : ∀ p1 p2 p3 p4 p5 : Point,
    p4 ≠ p5 →
    base.neutral.Cong p1 p4 p1 p5 →
    base.neutral.Cong p2 p4 p2 p5 →
    base.neutral.Cong p3 p4 p3 p5 →
    base.neutral.Bet p1 p2 p3 ∨
      base.neutral.Bet p2 p3 p1 ∨
      base.neutral.Bet p3 p1 p2

structure TarskiEuclidean2D (Point : Type) where
  plane : Tarski2D Point
  euclid : ∀ p1 p2 p3 p4 p5 : Point,
    plane.base.neutral.Bet p1 p4 p5 →
    plane.base.neutral.Bet p2 p4 p3 →
    p1 ≠ p4 →
      ∃ x y, plane.base.neutral.Bet p1 p2 x ∧
        plane.base.neutral.Bet p1 p3 y ∧
        plane.base.neutral.Bet x p5 y

end TarskiGeometryFromAxiomsSameMathInLean
