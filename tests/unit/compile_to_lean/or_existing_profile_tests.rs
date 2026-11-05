use super::or_order_builtin_tests::target;
use crate::prelude::*;
#[test]
fn existing_or_profiles_retain_their_original_eight_selected_builtin_variants() {
    let cases = [
        r#"# An integer in the closed interval from zero to two equals one of its endpoints or the middle value.
thm checked_integer_closed_interval_alternatives:
    ? forall x closed_range(0,2):
        x=0 or x=1 or x=2
    x=0 or x=1 or x=2
"#,
        r#"# An integer in the half-open interval from zero to three equals zero, one or two.
thm checked_integer_half_open_interval_alternatives:
    ? forall x range(0,3):
        x=0 or x=1 or x=2
    x=0 or x=1 or x=2
"#,
        r#"# Two real values are either equal or unequal.
thm checked_real_equality_excluded_middle:
    ? forall a,b R:
        a=b or a!=b
    a=b or a!=b
"#,
        r#"# A zero product of two real values has a zero factor.
thm checked_real_zero_product_alternatives:
    ? forall a,b R:
        a*b=0
        =>:
            a=0 or b=0
    a=0 or b=0
"#,
        r#"# Two real values admit a strict comparison or its reverse weak comparison.
thm checked_real_strict_or_reverse_weak:
    ? forall a,b R:
        a<b or a>=b
    a<b or a>=b
"#,
        r#"# Two real values admit a reverse strict comparison or a weak comparison.
thm checked_real_reverse_strict_or_weak:
    ? forall a,b R:
        a>b or a<=b
    a>b or a<=b
"#,
        r#"# An integer at least a given integer equals that boundary or strictly exceeds it.
thm checked_integer_lower_bound_alternatives:
    ? forall x,n Z:
        x>=n
        =>:
            x=n or x>n
    x=n or x>n
"#,
        r#"# A nonzero sum of two real squares has a nonzero component.
thm checked_real_nonzero_square_sum_alternatives:
    ? forall a,b R:
        a^2+b^2!=0
        =>:
            a!=0 or b!=0
    a!=0 or b!=0
"#,
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
