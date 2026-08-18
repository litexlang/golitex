/-
The same point-only Chapters 2--12 layer, Euclid I.5, exact angle-based SAS and
SSS-to-angle theorems, reflection construction, and parallel interfaces as
`main.lit`, expressed in pure Lean 4. Relations use functions into `Prop`
because Prelude does not provide the first-class relation-set notation used by
Litex.

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

def LinesHaveCommonPoint {Point : Type} (Bet : Betweenness Point)
    (line1A line1B line2A line2B : Point) : Prop :=
  ∃ intersection,
    Collinear Bet intersection line1A line1B ∧
      Collinear Bet intersection line2A line2B

def StrictlyParallel {Point : Type} (Bet : Betweenness Point)
    (line1A line1B line2A line2B : Point) : Prop :=
  line1A ≠ line1B ∧ line2A ≠ line2B ∧
    Coplanar Bet line1A line1B line2A line2B ∧
    ¬ LinesHaveCommonPoint Bet line1A line1B line2A line2B

def CoincidentNondegenerateLines {Point : Type} (Bet : Betweenness Point)
    (line1A line1B line2A line2B : Point) : Prop :=
  line1A ≠ line1B ∧ line2A ≠ line2B ∧
    Collinear Bet line1A line2A line2B ∧
    Collinear Bet line1B line2A line2B

def Parallel {Point : Type} (Bet : Betweenness Point)
    (line1A line1B line2A line2B : Point) : Prop :=
  StrictlyParallel Bet line1A line1B line2A line2B ∨
    CoincidentNondegenerateLines Bet line1A line1B line2A line2B

def EuclidIntersectionWitnessExists {Point : Type} (Bet : Betweenness Point)
    (rayStart firstRayPoint secondRayPoint betweenPoint : Point) : Prop :=
  ∃ firstIntersection secondIntersection,
    Bet rayStart firstRayPoint firstIntersection ∧
      Bet rayStart secondRayPoint secondIntersection ∧
      Bet firstIntersection betweenPoint secondIntersection

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

def InnerFiveSegmentConfiguration {Point : Type} (Bet : Betweenness Point)
    (Cong : SegmentCongruence Point)
    (a b c d a₂ b₂ c₂ d₂ : Point) : Prop :=
  Bet a b c ∧ Bet a₂ b₂ c₂ ∧ Cong a c a₂ c₂ ∧
    Cong b c b₂ c₂ ∧ Cong a d a₂ d₂ ∧ Cong c d c₂ d₂

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

theorem between_exchange {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c d : Point}
    (h₁ : G.Bet a b c) (h₂ : G.Bet a c d) : G.Bet b c d := by
  rcases G.innerPasch d c a c b (between_symmetric G h₂)
      (between_symmetric G h₁) with ⟨x, hcx, hbxd⟩
  have hx : c = x := G.betweenIdentity c x hcx
  simpa [hx] using hbxd

theorem out_on_ray_reflexive {Point : Type}
    (G : TarskiNeutralDimensionless Point) {vertex point : Point}
    (h : point ≠ vertex) : Out G.Bet vertex point point :=
  ⟨h, h, Or.inl (between_trivial G vertex point)⟩

theorem out_on_ray_symmetric {Point : Type} (Bet : Betweenness Point)
    {vertex firstPoint secondPoint : Point}
    (h : Out Bet vertex firstPoint secondPoint) :
    Out Bet vertex secondPoint firstPoint := by
  rcases h with ⟨hfirst, hsecond, hbet | hbet⟩
  · exact ⟨hsecond, hfirst, Or.inr hbet⟩
  · exact ⟨hsecond, hfirst, Or.inl hbet⟩

theorem out_on_ray_implies_collinear {Point : Type}
    (G : TarskiNeutralDimensionless Point)
    {vertex firstPoint secondPoint : Point}
    (h : Out G.Bet vertex firstPoint secondPoint) :
    Collinear G.Bet vertex firstPoint secondPoint := by
  rcases h.2.2 with hbet | hbet
  · exact Or.inl hbet
  · exact Or.inr (Or.inl (between_symmetric G hbet))

theorem point_has_strict_extension {Point : Type}
    (G : TarskiNeutralDimensionless Point) (a b : Point) :
    ∃ x, G.Bet a b x ∧ b ≠ x := by
  have hlower : G.lowerA ≠ G.lowerB := by
    intro h
    apply G.lowerDimension3
    simpa [h] using between_trivial G G.lowerC G.lowerA
  rcases G.segmentConstruction a b G.lowerA G.lowerB with
    ⟨x, hbet, hcong⟩
  refine ⟨x, hbet, ?_⟩
  intro h
  apply hlower
  have hsymmetric : G.Cong G.lowerA G.lowerB b x :=
    segment_congruence_symmetric G hcong
  have hdegenerate : G.Cong G.lowerA G.lowerB b b := by
    simpa [h] using hsymmetric
  exact G.congrIdentity G.lowerA G.lowerB b hdegenerate

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

theorem midpoint_has_congruent_halves {Point : Type}
    (Bet : Betweenness Point) (Cong : SegmentCongruence Point)
    {midpoint endpointA endpointB : Point}
    (h : IsMidpoint Bet Cong midpoint endpointA endpointB) :
    Cong endpointA midpoint midpoint endpointB :=
  h.2

theorem midpoint_symmetric {Point : Type}
    (G : TarskiNeutralDimensionless Point)
    {midpoint endpointA endpointB : Point}
    (h : IsMidpoint G.Bet G.Cong midpoint endpointA endpointB) :
    IsMidpoint G.Bet G.Cong midpoint endpointB endpointA :=
  ⟨between_symmetric G h.1,
    segment_congruence_symmetric G
      (segment_congruence_endpoint_commutative G h.2)⟩

theorem point_is_own_degenerate_midpoint {Point : Type}
    (G : TarskiNeutralDimensionless Point) (a : Point) :
    IsMidpoint G.Bet G.Cong a a a :=
  ⟨between_trivial G a a, segment_congruence_reflexive G a a⟩

theorem point_reflection_is_midpoint {Point : Type}
    (Bet : Betweenness Point) (Cong : SegmentCongruence Point)
    {point reflectedPoint center : Point}
    (h : PointReflection Bet Cong point reflectedPoint center) :
    IsMidpoint Bet Cong center point reflectedPoint :=
  h

theorem segment_extension_unique {Point : Type}
    (G : TarskiNeutralDimensionless Point)
    {q a b c x y : Point} (hqa : q ≠ a)
    (hqax : G.Bet q a x) (hax : G.Cong a x b c)
    (hqay : G.Bet q a y) (hay : G.Cong a y b c) : x = y := by
  have haxy : G.Cong a x a y :=
    segment_congruence_transitive G hax
      (segment_congruence_symmetric G hay)
  have hxy : G.Cong x y y y :=
    G.fiveSegment q q a a x y y y
      (segment_congruence_reflexive G q a) haxy
      (segment_congruence_reflexive G q y)
      (segment_congruence_reflexive G a y) hqax hqay hqa
  exact G.congrIdentity x y y hxy

theorem point_reflection_exists {Point : Type}
    (G : TarskiNeutralDimensionless Point) (point center : Point) :
    ∃ reflectedPoint, PointReflection G.Bet G.Cong point reflectedPoint center := by
  rcases G.segmentConstruction point center point center with
    ⟨reflectedPoint, hbet, hcong⟩
  exact ⟨reflectedPoint, hbet, segment_congruence_symmetric G hcong⟩

theorem point_reflection_fixes_center {Point : Type}
    (G : TarskiNeutralDimensionless Point) (center : Point) :
    PointReflection G.Bet G.Cong center center center :=
  point_is_own_degenerate_midpoint G center

theorem point_reflection_involutive {Point : Type}
    (G : TarskiNeutralDimensionless Point)
    {point reflectedPoint center : Point}
    (h : PointReflection G.Bet G.Cong point reflectedPoint center) :
    PointReflection G.Bet G.Cong reflectedPoint point center :=
  midpoint_symmetric G h

structure TarskiNeutralWithDecidableEquality (Point : Type) where
  neutral : TarskiNeutralDimensionless Point
  pointEqualityDecidable : ∀ p1 p2 : Point, p1 = p2 ∨ p1 ≠ p2

theorem point_reflection_unique {Point : Type}
    (G : TarskiNeutralWithDecidableEquality Point)
    {point center reflected1 reflected2 : Point}
    (h1 : PointReflection G.neutral.Bet G.neutral.Cong
      point reflected1 center)
    (h2 : PointReflection G.neutral.Bet G.neutral.Cong
      point reflected2 center) : reflected1 = reflected2 := by
  rcases G.pointEqualityDecidable point center with heq | hne
  · have hr1 : reflected1 = center := by
      have hdeg : G.neutral.Cong reflected1 center center center := by
        have hright : G.neutral.Cong center center reflected1 center :=
          segment_congruence_right_commutative G.neutral (by
            simpa [heq] using h1.2)
        exact segment_congruence_symmetric G.neutral hright
      exact G.neutral.congrIdentity reflected1 center center hdeg
    have hr2 : reflected2 = center := by
      have hdeg : G.neutral.Cong reflected2 center center center := by
        have hright : G.neutral.Cong center center reflected2 center :=
          segment_congruence_right_commutative G.neutral (by
            simpa [heq] using h2.2)
        exact segment_congruence_symmetric G.neutral hright
      exact G.neutral.congrIdentity reflected2 center center hdeg
    exact hr1.trans hr2.symm
  · exact segment_extension_unique G.neutral hne h1.1
      (segment_congruence_symmetric G.neutral h1.2) h2.1
      (segment_congruence_symmetric G.neutral h2.2)

theorem segment_congruence_addition {Point : Type}
    (G : TarskiNeutralWithDecidableEquality Point)
    {a b c a₂ b₂ c₂ : Point}
    (hbet : G.neutral.Bet a b c) (hbet₂ : G.neutral.Bet a₂ b₂ c₂)
    (hab : G.neutral.Cong a b a₂ b₂)
    (hbc : G.neutral.Cong b c b₂ c₂) :
    G.neutral.Cong a c a₂ c₂ := by
  rcases G.pointEqualityDecidable a b with heq | hne
  · have ha₂b₂ : a₂ = b₂ := by
      have hsymmetric : G.neutral.Cong a₂ b₂ a a := by
        simpa [heq] using segment_congruence_symmetric G.neutral hab
      exact G.neutral.congrIdentity a₂ b₂ a hsymmetric
    simpa [heq, ha₂b₂] using hbc
  · have hzero : G.neutral.Cong a a a₂ a₂ :=
      degenerate_segments_congruent G.neutral a a₂
    have hreverse : G.neutral.Cong b a b₂ a₂ :=
      segment_congruence_endpoint_commutative G.neutral hab
    have hca : G.neutral.Cong c a c₂ a₂ :=
      G.neutral.fiveSegment a a₂ b b₂ c c₂ a a₂
        hab hbc hzero hreverse hbet hbet₂ hne
    exact segment_congruence_endpoint_commutative G.neutral hca

theorem inner_five_segment {Point : Type}
    (G : TarskiNeutralWithDecidableEquality Point)
    {a b c d a₂ b₂ c₂ d₂ : Point}
    (h : InnerFiveSegmentConfiguration G.neutral.Bet G.neutral.Cong
      a b c d a₂ b₂ c₂ d₂) :
    G.neutral.Cong b d b₂ d₂ := by
  rcases h with ⟨habc, ha₂b₂c₂, hac, hbc, had, hcd⟩
  rcases G.pointEqualityDecidable a c with heq | hne
  · have ha₂c₂ : a₂ = c₂ := by
      have hsymmetric : G.neutral.Cong a₂ c₂ a a := by
        simpa [heq] using segment_congruence_symmetric G.neutral hac
      exact G.neutral.congrIdentity a₂ c₂ a hsymmetric
    have hab : a = b := by
      apply G.neutral.betweenIdentity a b
      simpa [heq] using habc
    have ha₂b₂ : a₂ = b₂ := by
      apply G.neutral.betweenIdentity a₂ b₂
      simpa [ha₂c₂] using ha₂b₂c₂
    simpa [hab, ha₂b₂] using had
  · rcases point_has_strict_extension G.neutral a c with
      ⟨extendedC, hacExtended, hcExtended⟩
    rcases G.neutral.segmentConstruction a₂ c₂ c extendedC with
      ⟨extendedC₂, ha₂c₂Extended, hconstructed⟩
    have hcExtendedCong : G.neutral.Cong c extendedC c₂ extendedC₂ :=
      segment_congruence_symmetric G.neutral hconstructed
    have hextendedD : G.neutral.Cong extendedC d extendedC₂ d₂ :=
      G.neutral.fiveSegment a a₂ c c₂ extendedC extendedC₂ d d₂
        hac hcExtendedCong had hcd hacExtended ha₂c₂Extended hne
    have hbcExtended : G.neutral.Bet b c extendedC :=
      between_exchange G.neutral habc hacExtended
    have hextendedCB : G.neutral.Bet extendedC c b :=
      between_symmetric G.neutral hbcExtended
    have hb₂c₂Extended : G.neutral.Bet b₂ c₂ extendedC₂ :=
      between_exchange G.neutral ha₂b₂c₂ ha₂c₂Extended
    have hextendedC₂B₂ : G.neutral.Bet extendedC₂ c₂ b₂ :=
      between_symmetric G.neutral hb₂c₂Extended
    have hextendedCCong : G.neutral.Cong extendedC c extendedC₂ c₂ :=
      segment_congruence_endpoint_commutative G.neutral hcExtendedCong
    have hcb : G.neutral.Cong c b c₂ b₂ :=
      segment_congruence_endpoint_commutative G.neutral hbc
    exact G.neutral.fiveSegment extendedC extendedC₂ c c₂ b b₂ d d₂
      hextendedCCong hcb hextendedD hcd hextendedCB hextendedC₂B₂
      hcExtended.symm

theorem side_angle_side_gives_third_side {Point : Type}
    (G : TarskiNeutralWithDecidableEquality Point)
    {a b c a₂ b₂ c₂ : Point}
    (hangle : AnglesCongruent G.neutral.Bet G.neutral.Cong
      a b c a₂ b₂ c₂)
    (hab : G.neutral.Cong a b a₂ b₂)
    (hbc : G.neutral.Cong b c b₂ c₂) :
    G.neutral.Cong a c a₂ c₂ := by
  rcases hangle with
    ⟨_, _, _, _, aExt, cExt, a₂Ext, c₂Ext,
      hbaExt, haaExt, hbcExt, hccExt,
      hb₂a₂Ext, ha₂a₂Ext, hb₂c₂Ext, hc₂c₂Ext, hextensions⟩
  have hba : G.neutral.Cong b a b₂ a₂ :=
    segment_congruence_endpoint_commutative G.neutral hab
  have hb₂a₂ba : G.neutral.Cong b₂ a₂ b a :=
    segment_congruence_symmetric G.neutral hba
  have haaExtBA : G.neutral.Cong a aExt b a :=
    segment_congruence_transitive G.neutral haaExt hb₂a₂ba
  have hbaA₂Ext : G.neutral.Cong b a a₂ a₂Ext :=
    segment_congruence_symmetric G.neutral ha₂a₂Ext
  have haaExtA₂Ext : G.neutral.Cong a aExt a₂ a₂Ext :=
    segment_congruence_transitive G.neutral haaExtBA hbaA₂Ext
  have hbaWhole : G.neutral.Cong b aExt b₂ a₂Ext :=
    segment_congruence_addition G hbaExt hb₂a₂Ext hba haaExtA₂Ext

  have hb₂c₂bc : G.neutral.Cong b₂ c₂ b c :=
    segment_congruence_symmetric G.neutral hbc
  have hccExtBC : G.neutral.Cong c cExt b c :=
    segment_congruence_transitive G.neutral hccExt hb₂c₂bc
  have hbcC₂Ext : G.neutral.Cong b c c₂ c₂Ext :=
    segment_congruence_symmetric G.neutral hc₂c₂Ext
  have hccExtC₂Ext : G.neutral.Cong c cExt c₂ c₂Ext :=
    segment_congruence_transitive G.neutral hccExtBC hbcC₂Ext
  have hbcWhole : G.neutral.Cong b cExt b₂ c₂Ext :=
    segment_congruence_addition G hbcExt hb₂c₂Ext hbc hccExtC₂Ext

  have hfirstConfiguration :
      InnerFiveSegmentConfiguration G.neutral.Bet G.neutral.Cong
        b a aExt cExt b₂ a₂ a₂Ext c₂Ext :=
    ⟨hbaExt, hb₂a₂Ext, hbaWhole, haaExtA₂Ext, hbcWhole, hextensions⟩
  have haCext : G.neutral.Cong a cExt a₂ c₂Ext :=
    inner_five_segment G hfirstConfiguration
  have hCextA : G.neutral.Cong cExt a c₂Ext a₂ :=
    segment_congruence_endpoint_commutative G.neutral haCext
  have hsecondConfiguration :
      InnerFiveSegmentConfiguration G.neutral.Bet G.neutral.Cong
        b c cExt a b₂ c₂ c₂Ext a₂ :=
    ⟨hbcExt, hb₂c₂Ext, hbcWhole, hccExtC₂Ext, hba, hCextA⟩
  have hca : G.neutral.Cong c a c₂ a₂ :=
    inner_five_segment G hsecondConfiguration
  exact segment_congruence_endpoint_commutative G.neutral hca

theorem triangle_congruence_sas {Point : Type}
    (G : TarskiNeutralWithDecidableEquality Point)
    {a b c a₂ b₂ c₂ : Point}
    (hangle : AnglesCongruent G.neutral.Bet G.neutral.Cong
      a b c a₂ b₂ c₂)
    (hab : G.neutral.Cong a b a₂ b₂)
    (hbc : G.neutral.Cong b c b₂ c₂) :
    TrianglesCongruent G.neutral.Cong a b c a₂ b₂ c₂ :=
  ⟨hab, side_angle_side_gives_third_side G hangle hab hbc, hbc⟩

theorem triangle_congruence_reflexive {Point : Type}
    (G : TarskiNeutralDimensionless Point) (a b c : Point) :
    TrianglesCongruent G.Cong a b c a b c :=
  ⟨segment_congruence_reflexive G a b,
    segment_congruence_reflexive G a c,
    segment_congruence_reflexive G b c⟩

theorem triangle_congruence_symmetric {Point : Type}
    (G : TarskiNeutralDimensionless Point) {a b c a₂ b₂ c₂ : Point}
    (h : TrianglesCongruent G.Cong a b c a₂ b₂ c₂) :
    TrianglesCongruent G.Cong a₂ b₂ c₂ a b c :=
  ⟨segment_congruence_symmetric G h.1,
    segment_congruence_symmetric G h.2.1,
    segment_congruence_symmetric G h.2.2⟩

theorem triangle_congruence_transitive {Point : Type}
    (G : TarskiNeutralDimensionless Point)
    {a b c a₂ b₂ c₂ a₃ b₃ c₃ : Point}
    (h1 : TrianglesCongruent G.Cong a b c a₂ b₂ c₂)
    (h2 : TrianglesCongruent G.Cong a₂ b₂ c₂ a₃ b₃ c₃) :
    TrianglesCongruent G.Cong a b c a₃ b₃ c₃ :=
  ⟨segment_congruence_transitive G h1.1 h2.1,
    segment_congruence_transitive G h1.2.1 h2.2.1,
    segment_congruence_transitive G h1.2.2 h2.2.2⟩

theorem triangle_congruence_sss_gives_angles {Point : Type}
    (G : TarskiNeutralWithDecidableEquality Point)
    {a b c a₂ b₂ c₂ : Point} (habne : a ≠ b) (hcbne : c ≠ b)
    (htri : TrianglesCongruent G.neutral.Cong a b c a₂ b₂ c₂) :
    AnglesCongruent G.neutral.Bet G.neutral.Cong a b c a₂ b₂ c₂ := by
  rcases htri with ⟨hab, hac, hbc⟩
  have ha₂b₂ : a₂ ≠ b₂ := by
    intro heq
    have hdeg : G.neutral.Cong a b a₂ a₂ := by simpa [heq] using hab
    exact habne (G.neutral.congrIdentity a b a₂ hdeg)
  have hc₂b₂ : c₂ ≠ b₂ := by
    intro heq
    have hdeg : G.neutral.Cong b c b₂ b₂ := by simpa [heq] using hbc
    exact hcbne (G.neutral.congrIdentity b c b₂ hdeg).symm
  rcases G.neutral.segmentConstruction b a b₂ a₂ with
    ⟨aExt, hbaExt, haaExt⟩
  rcases G.neutral.segmentConstruction b c b₂ c₂ with
    ⟨cExt, hbcExt, hccExt⟩
  rcases G.neutral.segmentConstruction b₂ a₂ b a with
    ⟨a₂Ext, hb₂a₂Ext, ha₂a₂Ext⟩
  rcases G.neutral.segmentConstruction b₂ c₂ b c with
    ⟨c₂Ext, hb₂c₂Ext, hc₂c₂Ext⟩

  have hba : G.neutral.Cong b a b₂ a₂ :=
    segment_congruence_endpoint_commutative G.neutral hab
  have haaExtBA : G.neutral.Cong a aExt b a :=
    segment_congruence_transitive G.neutral haaExt
      (segment_congruence_symmetric G.neutral hba)
  have hbaA₂Ext : G.neutral.Cong b a a₂ a₂Ext :=
    segment_congruence_symmetric G.neutral ha₂a₂Ext
  have haaExtA₂Ext : G.neutral.Cong a aExt a₂ a₂Ext :=
    segment_congruence_transitive G.neutral haaExtBA hbaA₂Ext
  have hbaWhole : G.neutral.Cong b aExt b₂ a₂Ext :=
    segment_congruence_addition G hbaExt hb₂a₂Ext hba haaExtA₂Ext

  have hccExtBC : G.neutral.Cong c cExt b c :=
    segment_congruence_transitive G.neutral hccExt
      (segment_congruence_symmetric G.neutral hbc)
  have hbcC₂Ext : G.neutral.Cong b c c₂ c₂Ext :=
    segment_congruence_symmetric G.neutral hc₂c₂Ext
  have hccExtC₂Ext : G.neutral.Cong c cExt c₂ c₂Ext :=
    segment_congruence_transitive G.neutral hccExtBC hbcC₂Ext

  have hfirst : G.neutral.Cong aExt c a₂Ext c₂ :=
    G.neutral.fiveSegment b b₂ a a₂ aExt a₂Ext c c₂
      hba haaExtA₂Ext hbc hac hbaExt hb₂a₂Ext habne.symm
  have hcaExt : G.neutral.Cong c aExt c₂ a₂Ext :=
    segment_congruence_endpoint_commutative G.neutral hfirst
  have hfinalReverse : G.neutral.Cong cExt aExt c₂Ext a₂Ext :=
    G.neutral.fiveSegment b b₂ c c₂ cExt c₂Ext aExt a₂Ext
      hbc hccExtC₂Ext hbaWhole hcaExt hbcExt hb₂c₂Ext hcbne.symm
  have hfinal : G.neutral.Cong aExt cExt a₂Ext c₂Ext :=
    segment_congruence_endpoint_commutative G.neutral hfinalReverse
  exact ⟨habne, hcbne, ha₂b₂, hc₂b₂,
    aExt, cExt, a₂Ext, c₂Ext,
    hbaExt, haaExt, hbcExt, hccExt,
    hb₂a₂Ext, ha₂a₂Ext, hb₂c₂Ext, hc₂c₂Ext, hfinal⟩

theorem angle_congruence_reflexive {Point : Type}
    (G : TarskiNeutralWithDecidableEquality Point) {a b c : Point}
    (hab : a ≠ b) (hcb : c ≠ b) :
    AnglesCongruent G.neutral.Bet G.neutral.Cong a b c a b c :=
  triangle_congruence_sss_gives_angles G hab hcb
    ⟨segment_congruence_reflexive G.neutral a b,
      segment_congruence_reflexive G.neutral a c,
      segment_congruence_reflexive G.neutral b c⟩

theorem angle_congruence_symmetric {Point : Type}
    (G : TarskiNeutralDimensionless Point)
    {a b c a₂ b₂ c₂ : Point}
    (h : AnglesCongruent G.Bet G.Cong a b c a₂ b₂ c₂) :
    AnglesCongruent G.Bet G.Cong a₂ b₂ c₂ a b c := by
  rcases h with ⟨hab, hcb, ha₂b₂, hc₂b₂,
    aExt, cExt, a₂Ext, c₂Ext,
    hbaExt, haaExt, hbcExt, hccExt,
    hb₂a₂Ext, ha₂a₂Ext, hb₂c₂Ext, hc₂c₂Ext, hfinal⟩
  exact ⟨ha₂b₂, hc₂b₂, hab, hcb,
    a₂Ext, c₂Ext, aExt, cExt,
    hb₂a₂Ext, ha₂a₂Ext, hb₂c₂Ext, hc₂c₂Ext,
    hbaExt, haaExt, hbcExt, hccExt,
    segment_congruence_symmetric G hfinal⟩

theorem angle_congruence_arms_commutative {Point : Type}
    (G : TarskiNeutralDimensionless Point)
    {a b c a₂ b₂ c₂ : Point}
    (h : AnglesCongruent G.Bet G.Cong a b c a₂ b₂ c₂) :
    AnglesCongruent G.Bet G.Cong c b a c₂ b₂ a₂ := by
  rcases h with ⟨hab, hcb, ha₂b₂, hc₂b₂,
    aExt, cExt, a₂Ext, c₂Ext,
    hbaExt, haaExt, hbcExt, hccExt,
    hb₂a₂Ext, ha₂a₂Ext, hb₂c₂Ext, hc₂c₂Ext, hfinal⟩
  exact ⟨hcb, hab, hc₂b₂, ha₂b₂,
    cExt, aExt, c₂Ext, a₂Ext,
    hbcExt, hccExt, hbaExt, haaExt,
    hb₂c₂Ext, hc₂c₂Ext, hb₂a₂Ext, ha₂a₂Ext,
    segment_congruence_endpoint_commutative G hfinal⟩

theorem parallel_lines_are_nondegenerate {Point : Type}
    (Bet : Betweenness Point) {line1A line1B line2A line2B : Point}
    (h : Parallel Bet line1A line1B line2A line2B) :
    line1A ≠ line1B ∧ line2A ≠ line2B := by
  rcases h with hstrict | hcoincident
  · exact ⟨hstrict.1, hstrict.2.1⟩
  · exact ⟨hcoincident.1, hcoincident.2.1⟩

theorem strict_parallel_lines_are_coplanar_and_disjoint {Point : Type}
    (Bet : Betweenness Point) {line1A line1B line2A line2B : Point}
    (h : StrictlyParallel Bet line1A line1B line2A line2B) :
    Coplanar Bet line1A line1B line2A line2B ∧
      ¬ LinesHaveCommonPoint Bet line1A line1B line2A line2B :=
  ⟨h.2.2.1, h.2.2.2⟩

theorem perpendicular_at_has_nondegenerate_lines_and_incidence {Point : Type}
    (Bet : Betweenness Point) (Cong : SegmentCongruence Point)
    {intersection line1A line1B line2A line2B : Point}
    (h : PerpendicularAt Bet Cong intersection line1A line1B line2A line2B) :
    line1A ≠ line1B ∧ line2A ≠ line2B ∧
      Collinear Bet intersection line1A line1B ∧
      Collinear Bet intersection line2A line2B :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem perpendicular_lines_are_nondegenerate {Point : Type}
    (Bet : Betweenness Point) (Cong : SegmentCongruence Point)
    {line1A line1B line2A line2B : Point}
    (h : LinesPerpendicular Bet Cong line1A line1B line2A line2B) :
    line1A ≠ line1B ∧ line2A ≠ line2B := by
  rcases h with ⟨intersection, hintersection⟩
  exact ⟨hintersection.1, hintersection.2.1⟩

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
      EuclidIntersectionWitnessExists plane.base.neutral.Bet p1 p2 p3 p5

theorem euclid_postulate_supplies_intersections {Point : Type}
    (G : TarskiEuclidean2D Point) {a b c d e : Point}
    (hade : G.plane.base.neutral.Bet a d e)
    (hbdc : G.plane.base.neutral.Bet b d c) (had : a ≠ d) :
    EuclidIntersectionWitnessExists G.plane.base.neutral.Bet a b c e :=
  G.euclid a b c d e hade hbdc had

end TarskiGeometryFromAxiomsSameMathInLean
