const IDENTITY: &str = r#"# The real identity is injective, surjective and bijective.
have fn identity(x R) R = x
claim:
    ? forall left, right R:
        identity(left) = identity(right)
        =>:
            left = right
    left = identity(left)
    identity(right) = right
    left = right
by def $injective(R, R, identity)
claim:
    ? forall target R:
        exist source R st {target = identity(source)}
    witness exist source R st {target = identity(source)} from target
by def $surjective(R, R, identity)
by def $bijective(R, R, identity)
"#;

use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByDefStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByDefinition, BuiltinPropDefinitionProof,
};
use crate::prelude::*;

fn definition(run: &mut RunLitexCodeResult) -> &mut ExecByDefStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
        &mut run.statement_results[2]
    else {
        panic!("injective by-def")
    };
    p
}

#[test]
fn mapping_properties_reject_changed_definition_and_wd() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(IDENTITY);
        let p = definition(&mut run);
        let VerifyFactResult::AtomicExceptEquality(result) = &mut p.proof else {
            panic!()
        };
        let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_mut() else {
            panic!()
        };
        if mutation == 0 {
            let PredicateDomainProof::ByRequirements(req) = &mut result
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .predicate_domain
            else {
                panic!()
            };
            req.pop();
        } else {
            let AtomicExceptEqualityFactSearchedProof::ByDefinition(
                AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
                    BuiltinPropDefinitionProof::Injective(proof),
                ),
            ) = &mut result.searched_proof
            else {
                panic!()
            };
            match mutation {
                1 => proof.proof_of_requirement_facts.clear(),
                2 => {
                    let Fact::ForallFact(f) = &mut proof.requirement_facts[0] else {
                        panic!()
                    };
                    f.dom_facts.clear();
                }
                3 => {
                    let Fact::ForallFact(f) = &mut proof.requirement_facts[0] else {
                        panic!()
                    };
                    f.typed_parameters.groups[0].params.swap(0, 1);
                }
                4 => {
                    let AtomicFact::InjectiveFact(f) = &mut result.fact else {
                        panic!()
                    };
                    f.codomain = Obj::StandardSet(StandardSet::C);
                }
                _ => unreachable!(),
            }
        }
        assert!(
            compiler.compile_run(&run, "mutated_mapping").is_err(),
            "mutation {mutation}"
        );
    }
}

fn preimage(run: &mut RunLitexCodeResult) -> &mut VerifyExistUniqueFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0] else {
        panic!()
    };
    let VerifyFactResult::ForallFact(p) = &mut p.verify_result else {
        panic!()
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = p.as_mut()
    else {
        panic!()
    };
    let VerifyFactResult::ExistShapedFact(p) = &mut p.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(p)) =
        p.as_mut()
    else {
        panic!()
    };
    p
}

#[test]
fn mapping_preimage_requires_exact_certificate_target_and_independent_witness() {
    use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::{
        ExistShapedFactSearchProofByBuiltinRule, ExistShapedFactSearchedProof,
    };
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(
            r#"# Every target of a bijection has exactly one preimage, in either equation orientation.
forall A, B set, f fn(t A)B, y B:
    $bijective(A, B, f)
    =>:
        exist! x A st {f(x) = y}
forall A, B set, f fn(t A)B, y B:
    $bijective(A, B, f)
    =>:
        exist! x A st {y = f(x)}
"#,
        );
        let p = preimage(&mut run);
        let ExistShapedFactSearchedProof::ByBuiltinRule(
            ExistShapedFactSearchProofByBuiltinRule::BijectivePreimage(e),
        ) = &mut p.searched_proof
        else {
            panic!("original builtin route")
        };
        match mutation {
            0 => {
                let AtomicFact::BijectiveFact(f) = &mut e.certificate.fact else {
                    panic!()
                };
                f.domain = Obj::StandardSet(StandardSet::R);
            }
            1 => {
                let VerifyFactResult::AtomicExceptEquality(r) = &mut e.target_membership else {
                    panic!()
                };
                let VerifyAtomicExceptEqualityFactResult::Success(r) = r.as_mut() else {
                    panic!()
                };
                let AtomicFact::InFact(f) = &mut r.fact else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::C);
            }
            2 => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) =
                    e.certificate.searched_proof.as_mut()
                else {
                    panic!()
                };
                c.why_parameters_of_known_fact_are_equal_to_givens.clear();
            }
            3 => {
                let ExistShapedFact::ExistUnique(s) = &mut p.fact else {
                    panic!()
                };
                let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut s.facts[0]
                else {
                    panic!()
                };
                eq.right = eq.left.clone();
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "invalid_preimage").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn mapping_inference_citations_obey_original_publication_order() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(IDENTITY);
    let p = definition(&mut run);
    let ids = p.stored.stored_fact_ids();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 3);
    for id in ids {
        assert!(compiler.cited_fact_reference(id, &before).is_err());
        assert!(compiler.cited_fact_reference(id, &after).is_ok());
    }
}
