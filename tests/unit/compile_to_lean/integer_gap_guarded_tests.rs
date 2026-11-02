use crate::prelude::*;

const GUARDED: &str = include_str!("../../../lean/examples/integer_gap_guarded/statement.lit");
const CACHED: &str = include_str!("../../../lean/examples/integer_gap_cached_guard/statement.lit");
const FUNCTION: &str =
    include_str!("../../../lean/examples/integer_gap_function_guard/statement.lit");

#[test]
fn guarded_integer_gap_replays_division_power_cached_and_function_wd() {
    for source in [GUARDED, CACHED, FUNCTION] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "guarded_gap").unwrap();
        assert!(lean.contains("Litex.integerGapLe"));
        assert!(lean.contains("nativeNonzeroOfDenote"));
        assert!(lean.contains("litex_normalize_rational"));
        assert_eq!(lean, compiler.compile_run(&run, "guarded_gap").unwrap());
    }
}

#[test]
fn guarded_integer_gap_resolves_the_original_cached_quotient_wd() {
    let (mut run, compiler) = super::execute(CACHED);
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[1].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Add(sum),
            ),
        ..
    } = atomic
        .well_defined_proof
        .detailed_ref()
        .well_defined_of_each_parameter[0]
        .detailed_ref()
    else {
        panic!("formed addition")
    };
    assert!(matches!(
        sum.child_obj_well_defined[0].detailed_ref(),
        DetailedObjWellDefinedProof::ByKnown { .. }
    ));
    compiler.compile_run(&run, "cached_guard").unwrap();
}

fn original_guard(wd: &mut ObjWellDefinedProof, power: bool) -> Option<&mut Vec<VerifyFactResult>> {
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ArithmeticOperator(proof),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        return None;
    };
    use ArithmeticOperatorObjWellDefinedProofByDef as A;
    let children = match proof {
        A::Add(p) => &mut p.child_obj_well_defined,
        A::Sub(p) => &mut p.child_obj_well_defined,
        A::Mul(p) => &mut p.child_obj_well_defined,
        A::Div(p) => {
            if !power {
                return Some(&mut p.requirement_fact_verified);
            }
            &mut p.child_obj_well_defined
        }
        A::Pow(p) => {
            if power {
                return Some(&mut p.requirement_fact_verified);
            }
            &mut p.child_obj_well_defined
        }
        _ => return None,
    };
    children
        .iter_mut()
        .find_map(|child| original_guard(child, power))
}

#[test]
fn guarded_integer_gap_requires_original_nonzero_subject_stage_and_citation() {
    for power in [false, true] {
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(GUARDED);
            let forall =
                super::forall_proof_mut(&mut run.statement_results[if power { 4 } else { 0 }]);
            let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
            let future = atomic.fact.fact_id();
            let wd = &mut atomic
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter[0];
            let requirements = original_guard(wd, power).expect("original denominator/base WD");
            let slot = if power { 2 } else { 0 };
            match mutation {
                0 => {
                    requirements.remove(slot);
                }
                1 => {
                    requirements.swap(slot, if power { 0 } else { 1 });
                }
                2 => {
                    let checked = super::atomic_proof_mut(&mut requirements[slot]);
                    let AtomicFact::NotEqualFact(fact) = &mut checked.fact else {
                        panic!()
                    };
                    fact.left = super::number_object("0");
                }
                3 => {
                    let checked = super::atomic_proof_mut(&mut requirements[slot]);
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut checked.searched_proof
                    else {
                        panic!("original nonzero citation")
                    };
                    cite.cite_fact_id = future;
                }
                _ => unreachable!(),
            }
            compiler
                .compile_run(&run, "forged_guard")
                .expect_err("original guarded WD is mandatory");
        }
    }
}
