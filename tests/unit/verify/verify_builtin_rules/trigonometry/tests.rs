use super::*;

#[test]
fn derived_trig_lemmas_are_strictly_above_their_core_dependencies() {
    for lemma in [
        TrigLemma::Parity,
        TrigLemma::Difference,
        TrigLemma::DoubleAngle,
        TrigLemma::SpecialPiValues,
        TrigLemma::Cofunction,
        TrigLemma::ShiftAndPeriod,
        TrigLemma::Bounds,
        TrigLemma::TanCotRelations,
    ] {
        assert!(lemma.level() > 0);
    }
    for lemma in [
        TrigLemma::CoreValues,
        TrigLemma::Addition,
        TrigLemma::UnitCircle,
        TrigLemma::Orientation,
        TrigLemma::QuotientDefinition,
    ] {
        assert_eq!(lemma.level(), 0);
    }
}
