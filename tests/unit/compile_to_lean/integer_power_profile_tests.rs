use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::prelude::*;
const CASES: [(&str, &str); 3] = [
    (
        r#"forall a C,m,n Z:
    a!=0
    =>:
        a^m*a^n=a^(m+n)
"#,
        "integerPowerProductValue",
    ),
    (
        r#"forall a C,m,n Z:
    a!=0
    =>:
        (a^m)^n=a^(m*n)
"#,
        "integerPowerOfPowerValue",
    ),
    (
        r#"forall a,b C,n Z:
    a!=0
    b!=0
    =>:
        (a*b)^n=a^n*b^n
"#,
        "integerPowerProductDistributionValue",
    ),
];
fn target(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn requirements(proof: &mut VerifyEqualitySuccess, index: usize) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByBuiltinRule(rule) = &mut proof.searched_proof else {
        panic!("selected power law")
    };
    match (rule, index) {
        (EqualitySearchProofByBuiltinRule::PowerProductSameBase(p), 0) => {
            &mut p.proof_of_requirement_facts
        }
        (EqualitySearchProofByBuiltinRule::PowerOfPower(p), 1) => &mut p.proof_of_requirement_facts,
        (EqualitySearchProofByBuiltinRule::PowerOfProduct(p), 2) => {
            &mut p.proof_of_requirement_facts
        }
        _ => panic!("exact selected integer power-law profile"),
    }
}
#[test]
fn integer_power_profiles_replay_original_nonzero_and_integer_requirements_in_both_equation_orientations(
) {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        let (prefix, last) = source.trim_end().rsplit_once('\n').unwrap();
        let (left, right) = last.trim().split_once('=').unwrap();
        let reversed = format!("{prefix}\n        {right}={left}\n");
        for source in [source, &reversed] {
            let (mut run, compiler) = super::execute(source);
            assert_eq!(
                requirements(target(&mut run), index).len(),
                if index == 2 { 5 } else { 4 }
            );
            let output = compiler
                .compile_run(&run, "integer_power_profile")
                .unwrap_or_else(|e| panic!("{source}: {e}"));
            assert!(output.contains(&format!("Litex.{law}")));
            assert_eq!(
                output,
                compiler.compile_run(&run, "integer_power_profile").unwrap()
            );
        }
    }
}
#[test]
fn integer_power_profiles_cannot_omit_swap_weaken_or_cite_future_nonzero_evidence() {
    for (index, (source, _)) in CASES.into_iter().enumerate() {
        for change in ["missing", "swapped", "carrier", "future", "wd"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            let future = p.fact.fact_id;
            if change == "wd" {
                let wd = p.well_defined_proof.as_detailed_mut().unwrap();
                std::mem::swap(&mut wd.left, &mut wd.right);
            } else {
                let children = requirements(p, index);
                let nonzero = if index == 2 { 3 } else { 1 };
                let exponent = 2;
                match change {
                    "missing" => {
                        children.pop();
                    }
                    "swapped" => children.swap(nonzero, exponent),
                    "carrier" => {
                        let AtomicFact::InFact(f) =
                            &mut super::atomic_proof_mut(&mut children[exponent]).fact
                        else {
                            panic!()
                        };
                        f.set = Obj::StandardSet(StandardSet::R);
                    }
                    "future" => {
                        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                            &mut super::atomic_proof_mut(&mut children[nonzero]).searched_proof
                        else {
                            panic!("original nonzero citation")
                        };
                        cite.cite_fact_id = future;
                    }
                    _ => unreachable!(),
                }
            }
            compiler.compile_run(&run,change).expect_err("keep exact original integer exponent memberships, nonzero bases, scoped citations and constructors");
        }
    }
}
