use super::or_order_builtin_tests::target;
use crate::prelude::*;
#[test]
fn existing_or_profiles_retain_their_original_eight_selected_builtin_variants() {
    let cases = [
        include_str!("../../../lean/examples/integer_closed_interval_alternatives/statement.lit"),
        include_str!(
            "../../../lean/examples/integer_half_open_interval_alternatives/statement.lit"
        ),
        include_str!("../../../lean/examples/real_equality_excluded_middle/statement.lit"),
        include_str!("../../../lean/examples/real_zero_product_alternatives/statement.lit"),
        include_str!("../../../lean/examples/real_strict_or_reverse_weak/statement.lit"),
        include_str!("../../../lean/examples/real_reverse_strict_or_weak/statement.lit"),
        include_str!("../../../lean/examples/integer_lower_bound_alternatives/statement.lit"),
        include_str!("../../../lean/examples/real_nonzero_square_sum_alternatives/statement.lit"),
    ];
    for (index, source) in cases.into_iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        let OrFactSearchedProof::ByBuiltinRule(p) = &target(&mut run).searched_proof else {
            panic!("original builtin proof")
        };
        assert!(matches!(
            (index, p),
            (
                0,
                OrFactSearchProofByBuiltinRule::ClosedIntegerRangeEqualityCover(_)
            ) | (
                1,
                OrFactSearchProofByBuiltinRule::HalfOpenIntegerRangeEqualityCover(_)
            ) | (2, OrFactSearchProofByBuiltinRule::ComplementaryAtomic(_))
                | (3, OrFactSearchProofByBuiltinRule::ZeroProductSplit(_))
                | (4, OrFactSearchProofByBuiltinRule::LessOrGreaterEqual(_))
                | (5, OrFactSearchProofByBuiltinRule::GreaterOrLessEqual(_))
                | (6, OrFactSearchProofByBuiltinRule::IntegerSuccessorTail(_))
                | (
                    7,
                    OrFactSearchProofByBuiltinRule::SquareSumComponentNonzero(_)
                )
        ));
        let output = compiler.compile_run(&run, "existing_or").unwrap();
        assert_eq!(output, compiler.compile_run(&run, "existing_or").unwrap());
    }
}
