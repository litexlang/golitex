/-
The same point-only Chapters 2--11 layer and Euclid I.5 as `main.lit`,
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

def TrianglesCongruent {Point : Type} (Cong : SegmentCongruence Point)
    (a b c d e f : Point) : Prop :=
  Cong a b d e ∧ Cong a c d f ∧ Cong b c e f

def SegmentLe {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point) (a b c d : Point) : Prop :=
  ∃ witness, Bet c witness d ∧ Cong a b c witness

def SegmentLt {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point) (a b c d : Point) : Prop :=
  SegmentLe Bet Cong a b c d ∧ ¬ Cong a b c d

def Out {Point : Type} (Bet : Betweenness Point)
    (vertex firstPoint secondPoint : Point) : Prop :=
  firstPoint ≠ vertex ∧ secondPoint ≠ vertex ∧
    (Bet vertex firstPoint secondPoint ∨ Bet vertex secondPoint firstPoint)

def RightAngle {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point) (pointA vertex pointC : Point) : Prop :=
  ∃ reflectedC, IsMidpoint Bet Cong vertex pointC reflectedC ∧
    Cong pointA pointC pointA reflectedC

def PerpendicularAt {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point)
    (intersection line1A line1B line2A line2B : Point) : Prop :=
  line1A ≠ line1B ∧ line2A ≠ line2B ∧
    Collinear Bet intersection line1A line1B ∧
    Collinear Bet intersection line2A line2B ∧
    ∀ pointU pointV,
      Collinear Bet pointU line1A line1B →
      Collinear Bet pointV line2A line2B →
      RightAngle Bet Cong pointU intersection pointV

def LinesPerpendicular {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point)
    (line1A line1B line2A line2B : Point) : Prop :=
  ∃ intersection,
    PerpendicularAt Bet Cong intersection line1A line1B line2A line2B

def OppositeSides {Point : Type} (Bet : Betweenness Point)
    (lineA lineB pointP pointQ : Point) : Prop :=
  ¬ Collinear Bet pointP lineA lineB ∧
  ¬ Collinear Bet pointQ lineA lineB ∧
  ∃ crossing, Collinear Bet crossing lineA lineB ∧ Bet pointP crossing pointQ

def PointReflection {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point)
    (point reflectedPoint center : Point) : Prop :=
  IsMidpoint Bet Cong center point reflectedPoint

def SameSide {Point : Type} (Bet : Betweenness Point)
    (lineA lineB pointP pointQ : Point) : Prop :=
  ∃ referencePoint,
    OppositeSides Bet lineA lineB pointP referencePoint ∧
    OppositeSides Bet lineA lineB pointQ referencePoint

def LinePairsSharePoint {Point : Type} (Bet : Betweenness Point)
    (line1A line1B line2A line2B intersection : Point) : Prop :=
  Collinear Bet line1A line1B intersection ∧
    Collinear Bet line2A line2B intersection

def CoplanarityWitness {Point : Type} (Bet : Betweenness Point)
    (a b c d intersection : Point) : Prop :=
  LinePairsSharePoint Bet a b c d intersection ∨
  LinePairsSharePoint Bet a c b d intersection ∨
  LinePairsSharePoint Bet a d b c intersection

def Coplanar {Point : Type} (Bet : Betweenness Point)
    (a b c d : Point) : Prop :=
  ∃ intersection, CoplanarityWitness Bet a b c d intersection

def LineReflectionAxisHit {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point)
    (point reflectedPoint lineA lineB : Point) : Prop :=
  ∃ intersection, IsMidpoint Bet Cong intersection point reflectedPoint ∧
    Collinear Bet lineA lineB intersection

def LineReflection {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point)
    (point reflectedPoint lineA lineB : Point) : Prop :=
  LineReflectionAxisHit Bet Cong point reflectedPoint lineA lineB ∧
    (LinesPerpendicular Bet Cong lineA lineB point reflectedPoint ∨
      point = reflectedPoint)

def Reflection {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point)
    (point reflectedPoint lineA lineB : Point) : Prop :=
  (lineA ≠ lineB ∧ LineReflection Bet Cong point reflectedPoint lineA lineB) ∨
  (lineA = lineB ∧ IsMidpoint Bet Cong lineA point reflectedPoint)

def AnglesCongruent {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point)
    (pointA vertexB pointC pointD vertexE pointF : Point) : Prop :=
  pointA ≠ vertexB ∧ pointC ≠ vertexB ∧
  pointD ≠ vertexE ∧ pointF ≠ vertexE ∧
  ∃ aExt cExt dExt fExt,
    Bet vertexB pointA aExt ∧ Cong pointA aExt vertexE pointD ∧
    Bet vertexB pointC cExt ∧ Cong pointC cExt vertexE pointF ∧
    Bet vertexE pointD dExt ∧ Cong pointD dExt vertexB pointA ∧
    Bet vertexE pointF fExt ∧ Cong pointF fExt vertexB pointC ∧
    Cong aExt cExt dExt fExt

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

theorem segment_congruence_transitive {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c d e f : Point}
    (h₁ : G.Cong a b c d) (h₂ : G.Cong c d e f) :
    G.Cong a b e f :=
  G.congrInnerTransitivity c d a b e f
    (segment_congruence_symmetric G h₁) h₂

theorem segment_congruence_left_commutative {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c d : Point}
    (h : G.Cong a b c d) : G.Cong b a c d :=
  G.congrInnerTransitivity a b b a c d
    (G.congrPseudoReflexivity a b) h

theorem segment_congruence_right_commutative {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c d : Point}
    (h : G.Cong a b c d) : G.Cong a b d c :=
  segment_congruence_symmetric G
    (segment_congruence_left_commutative G
      (segment_congruence_symmetric G h))

theorem segment_congruence_endpoint_commutative {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c d : Point}
    (h : G.Cong a b c d) : G.Cong b a d c :=
  segment_congruence_right_commutative G
    (segment_congruence_left_commutative G h)

theorem between_trivial {Point : Type}
    (G : TarskiNeutralDimensionless Point) (a b : Point) : G.Bet a b b := by
  rcases G.segmentConstruction a b b b with ⟨x, hbet, hcong⟩
  have hx : b = x := G.congrIdentity b x b hcong
  simpa [hx] using hbet

theorem between_symmetric {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c : Point}
    (h : G.Bet a b c) : G.Bet c b a := by
  rcases G.innerPasch a b c b c h (between_trivial G b c) with
    ⟨x, hbx, hcx⟩
  have hx : b = x := G.betweenIdentity b x hbx
  simpa [hx] using hcx

theorem noncollinear_points_are_pairwise_distinct {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c : Point}
    (hcol : ¬ Collinear G.Bet a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  have hab : a ≠ b := by
    intro h
    apply hcol
    subst b
    exact Or.inr (Or.inr (between_trivial G c a))
  have hbc : b ≠ c := by
    intro h
    apply hcol
    subst c
    exact Or.inl (between_trivial G a b)
  have hac : a ≠ c := by
    intro h
    apply hcol
    subst c
    exact Or.inr (Or.inl (between_trivial G b a))
  exact ⟨hab, hbc, hac⟩

theorem degenerate_segments_congruent {Point : Type}
    (G : TarskiNeutralDimensionless Point) (a b : Point) :
    G.Cong a a b b := by
  rcases G.segmentConstruction a a b b with ⟨x, _, hcong⟩
  have hx : a = x := G.congrIdentity a x b hcong
  simpa [hx] using hcong

theorem opposite_extensions_preserve_distances {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c cExt fExt : Point}
    (hcExt : G.Bet a c cExt) (hccExt : G.Cong c cExt c a)
    (hfExt : G.Bet c a fExt) (hafExt : G.Cong a fExt a c)
    (hab : G.Cong a b c b) (hac : a ≠ c) :
    G.Cong a cExt c fExt ∧ G.Cong b cExt b fExt := by
  have hcaaf : G.Cong c a a fExt :=
    segment_congruence_left_commutative G
      (segment_congruence_symmetric G hafExt)
  have hccaf : G.Cong c cExt a fExt :=
    segment_congruence_transitive G hccExt hcaaf
  have hzero : G.Cong a a c c := degenerate_segments_congruent G a c
  have hfirst : G.Cong cExt a fExt c :=
    G.fiveSegment a c c a cExt fExt a c
      (G.congrPseudoReflexivity a c) hccaf hzero
      (G.congrPseudoReflexivity c a) hcExt hfExt hac
  have hsecond : G.Cong cExt b fExt b :=
    G.fiveSegment a c c a cExt fExt b b
      (G.congrPseudoReflexivity a c) hccaf hab
      (segment_congruence_symmetric G hab) hcExt hfExt hac
  exact ⟨segment_congruence_endpoint_commutative G hfirst,
    segment_congruence_endpoint_commutative G hsecond⟩

theorem isosceles_triangle_has_equal_base_angles {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c : Point}
    (hcol : ¬ Collinear G.Bet a b c) (hiso : G.Cong b a b c) :
    AnglesCongruent G.Bet G.Cong b a c b c a := by
  rcases noncollinear_points_are_pairwise_distinct G hcol with
    ⟨hab, hbc, hac⟩
  have habcb : G.Cong a b c b :=
    segment_congruence_endpoint_commutative G hiso
  rcases G.segmentConstruction a b c b with ⟨aExt, haBet, haCong⟩
  rcases G.segmentConstruction a c c a with ⟨cExt, hcBet, hcCong⟩
  rcases G.segmentConstruction c b a b with ⟨dExt, hdBet, hdCong⟩
  rcases G.segmentConstruction c a a c with ⟨fExt, hfBet, hfCong⟩
  rcases opposite_extensions_preserve_distances G hcBet hcCong hfBet hfCong
      habcb hac with ⟨hacross, hbcross⟩
  have hbaab : G.Cong b aExt a b :=
    segment_congruence_transitive G haCong
      (segment_congruence_symmetric G habcb)
  have habbd : G.Cong a b b dExt :=
    segment_congruence_symmetric G hdCong
  have hbad : G.Cong b aExt b dExt :=
    segment_congruence_transitive G hbaab habbd
  have hfinal : G.Cong aExt cExt dExt fExt :=
    G.fiveSegment a c b b aExt dExt cExt fExt
      habcb hbad hacross hbcross haBet hdBet hab
  exact ⟨hab.symm, hac.symm, hbc, hac,
    aExt, cExt, dExt, fExt,
    haBet, haCong, hcBet, hcCong, hdBet, hdCong, hfBet, hfCong, hfinal⟩

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
