use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_extra::ScalarExtraEqualityProof as Rule;
use crate::prelude::*;

const CASES: [(&str, &str); 2] = [
    (
        include_str!("../../../lean/examples/square_root_known_product/statement.lit"),
        "sqrtProductFromArgumentEquality",
    ),
    (
        include_str!("../../../lean/examples/square_root_known_quotient/statement.lit"),
        "sqrtQuotientFromArgumentEquality",
    ),
];
const GENERAL:[&str;2]=[
    "forall a,b,x R:\n    0<=a\n    0<=b\n    0<=x\n    x=a*b\n    =>:\n        sqrt(x)=sqrt(a)*sqrt(b)\n",
    "forall a,b,x R:\n    0<=a\n    0<b\n    0<=x\n    x=a/b\n    =>:\n        sqrt(x)=sqrt(a)/sqrt(b)\n",
];
fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn evidence(proof: &mut VerifyEqualitySuccess, index: usize) -> &mut EqualFactSearchedProof {
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ScalarExtra(rule)) =
        &mut proof.searched_proof
    else {
        panic!("selected scalar-extra known-argument rule")
    };
    match (rule, index) {
        (Rule::SqrtProductFromKnownArgument(p), 0) => &mut p.argument_equality,
        (Rule::SqrtQuotientFromKnownArgument(p), 1) => &mut p.argument_equality,
        _ => panic!("exact selected known-argument variant"),
    }
}

#[test]
fn both_known_root_argument_rules_replay_original_equality_and_parent_wd() {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        for source in [source, GENERAL[index]] {
            let (mut run, compiler) = super::execute(source);
            evidence(equality(&mut run), index);
            let output = compiler
                .compile_run(&run, "known_root_argument")
                .unwrap_or_else(|e| panic!("{source}: {e}"));
            assert!(output.contains(&format!("Litex.{law}")));
            assert_eq!(
                output,
                compiler.compile_run(&run, "known_root_argument").unwrap()
            );
        }
    }
}

#[test]
fn known_root_arguments_preserve_both_equation_orientations() {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        let (prefix, last) = source.trim_end().rsplit_once('\n').unwrap();
        let (left, right) = last.trim().split_once('=').unwrap();
        let source = format!("{prefix}\n        {right}={left}\n");
        let (mut run, compiler) = super::execute(&source);
        evidence(equality(&mut run), index);
        assert!(compiler
            .compile_run(&run, "reverse_known_root_argument")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
}

#[test]
fn known_root_argument_paths_cannot_be_missing_reversed_future_or_foreign() {
    for (index, (source, _)) in CASES.into_iter().enumerate() {
        for change in ["missing", "reversed", "future", "wd"] {
            let (mut run, compiler) = super::execute(source);
            let p = equality(&mut run);
            let future = p.fact.fact_id;
            if change == "wd" {
                let p = p.well_defined_proof.as_detailed_mut().unwrap();
                std::mem::swap(&mut p.left, &mut p.right);
            } else {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) = evidence(p, index)
                else {
                    panic!("original argument equality path")
                };
                assert!(!path.path.is_empty());
                match change {
                    "missing" => path.path.clear(),
                    "future" => path.path[0].2 = future,
                    "reversed" => {
                        let (a, b, _) = &mut path.path[0];
                        std::mem::swap(a, b);
                    }
                    _ => unreachable!(),
                }
            }
            compiler.compile_run(&run,change).expect_err("original exact argument equality, prior citation and parent constructors must be preserved");
        }
    }
}
