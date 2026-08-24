use super::*;

#[test]
fn membership_projection_candidates_are_proper_and_target_driven() {
    let complex_sources = StandardSet::C.proper_subsets_in_membership_proof_order();
    assert!(complex_sources.contains(&StandardSet::N));
    assert!(complex_sources.contains(&StandardSet::Z));
    assert!(complex_sources.contains(&StandardSet::Q));
    assert!(complex_sources.contains(&StandardSet::R));
    assert!(complex_sources.contains(&StandardSet::CStar));
    assert!(!complex_sources.contains(&StandardSet::C));
    assert_eq!(
        &complex_sources[..4],
        &[
            StandardSet::N,
            StandardSet::Z,
            StandardSet::Q,
            StandardSet::R,
        ]
    );

    let real_sources = StandardSet::R.proper_subsets_in_membership_proof_order();
    assert!(!real_sources.contains(&StandardSet::C));
    assert!(!real_sources.contains(&StandardSet::CStar));

    for target in [
        StandardSet::NPos,
        StandardSet::N,
        StandardSet::ZNeg,
        StandardSet::ZStar,
        StandardSet::Z,
        StandardSet::QPos,
        StandardSet::QNeg,
        StandardSet::QStar,
        StandardSet::Q,
        StandardSet::RPos,
        StandardSet::RNeg,
        StandardSet::RStar,
        StandardSet::R,
        StandardSet::CStar,
        StandardSet::C,
    ] {
        for source in target.proper_subsets_in_membership_proof_order() {
            assert_ne!(source, target);
            assert!(source.is_subset_eq(&target));
        }
    }
}
