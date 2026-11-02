use crate::compile_to_lean::helper::source_subject;
use crate::prelude::*;

pub(super) const SOURCES51:&[(&str,&str)]=&[
("compound","forall sc51e_a,sc51e_b,sc51e_c,sc51e_p,sc51e_q R:\n    abs(sc51e_a*sc51e_b)=sc51e_p\n    abs(sc51e_c)=sc51e_q\n    =>:\n        abs((sc51e_a*sc51e_b)*sc51e_c)=sc51e_p*sc51e_q\n"),
("direct","forall sc51a_a,sc51a_b,sc51a_p,sc51a_q R:\n    abs(sc51a_a)=sc51a_p\n    abs(sc51a_b)=sc51a_q\n    =>:\n        abs(sc51a_a*sc51a_b)=sc51a_p*sc51a_q\n"),
("generic_magnitudes","forall sc51j_a,sc51j_b R,sc51j_p,sc51j_q set:\n    abs(sc51j_a)=sc51j_p\n    abs(sc51j_b)=sc51j_q\n    =>:\n        abs(sc51j_a*sc51j_b)=sc51j_p*sc51j_q\n"),
("input_reversed","forall sc51i_a,sc51i_b,sc51i_p,sc51i_q R:\n    abs(sc51i_a)=sc51i_p\n    abs(sc51i_b)=sc51i_q\n    =>:\n        abs(sc51i_b*sc51i_a)=sc51i_p*sc51i_q\n"),
("integer","forall sc51k_a,sc51k_b,sc51k_p,sc51k_q Z:\n    abs(sc51k_a)=sc51k_p\n    abs(sc51k_b)=sc51k_q\n    =>:\n        abs(sc51k_a*sc51k_b)=sc51k_p*sc51k_q\n"),
("repeated","forall sc51f_a,sc51f_p R:\n    abs(sc51f_a)=sc51f_p\n    =>:\n        abs(sc51f_a*sc51f_a)=sc51f_p*sc51f_p\n"),
("returned","forall sc51d_f fn(sc51d_t R) R,sc51d_t,sc51d_b,sc51d_p,sc51d_q R:\n    abs(sc51d_f(sc51d_t))=sc51d_p\n    abs(sc51d_b)=sc51d_q\n    =>:\n        abs(sc51d_f(sc51d_t)*sc51d_b)=sc51d_p*sc51d_q\n"),
("reverse","forall sc51b_a,sc51b_b,sc51b_p,sc51b_q R:\n    abs(sc51b_a)=sc51b_p\n    abs(sc51b_b)=sc51b_q\n    =>:\n        sc51b_p*sc51b_q=abs(sc51b_a*sc51b_b)\n"),
("reverse_swapped","forall sc51h_a,sc51h_b,sc51h_p,sc51h_q R:\n    abs(sc51h_a)=sc51h_p\n    abs(sc51h_b)=sc51h_q\n    =>:\n        sc51h_q*sc51h_p=abs(sc51h_a*sc51h_b)\n"),
("reversed_premises","forall sc51g_a,sc51g_b,sc51g_p,sc51g_q R:\n    sc51g_p=abs(sc51g_a)\n    sc51g_q=abs(sc51g_b)\n    =>:\n        abs(sc51g_a*sc51g_b)=sc51g_p*sc51g_q\n"),
("swapped","forall sc51c_a,sc51c_b,sc51c_p,sc51c_q R:\n    abs(sc51c_a)=sc51c_p\n    abs(sc51c_b)=sc51c_q\n    =>:\n        abs(sc51c_a*sc51c_b)=sc51c_q*sc51c_p\n")];

#[test]
fn abs_product_strategy_original_typed_audit() {
    for (name, source) in SOURCES51 {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(run.statement_results.last().unwrap());
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::AbsProductFromFactors(p),
        ) = &equal.searched_proof
        else {
            panic!("selected strategy:{name}")
        };
        assert_eq!(p.requirement_facts.len(), 2);
        assert_eq!(p.proof_of_requirement_facts.len(), 2);
        eprintln!("ORIGINAL51 {name} goal:{}", equal.fact.ir());
        for (index, (requirement, child)) in p
            .requirement_facts
            .iter()
            .zip(&p.proof_of_requirement_facts)
            .enumerate()
        {
            assert_eq!(source_subject(child).unwrap(), *requirement);
            let child = super::equality_proof(child);
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = requirement else {
                panic!()
            };
            assert!(matches!(
                f.left,
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))
            ));
            let kind = match &child.searched_proof {
                EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) => {
                    eprintln!(
                        "ORIGINAL51 {name} child:{index} citations:{:?}",
                        path.path.iter().map(|x| x.2.value()).collect::<Vec<_>>()
                    );
                    "KnownPath"
                }
                _ => "OtherOriginal",
            };
            eprintln!(
                "ORIGINAL51 {name} child:{index} fact:{} subject:{} route:{kind}",
                requirement.fact_id().value(),
                requirement.ir()
            );
        }
        assert!(compiler
            .compile_run(&run, "Abs51OriginalAudit")
            .unwrap()
            .contains("Litex.absProduct"));
    }
}

fn source51(name: &str) -> &'static str {
    SOURCES51.iter().find(|(n, _)| *n == name).unwrap().1
}
fn selected51(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_by_composed_structure::AbsProductFromFactorsProof{
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal =
        super::equality_proof_mut(&mut outer.proved_then_facts.last_mut().unwrap().verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::AbsProductFromFactors(p),
    ) = &mut equal.searched_proof
    else {
        panic!("selected abs product")
    };
    p
}
fn change_citation51(child: &mut VerifyFactResult, id: FactId) {
    let equal = super::equality_proof_mut(child);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut equal.searched_proof
    else {
        panic!("original path")
    };
    assert_eq!(path.path.len(), 1);
    path.path[0].2 = id;
}

#[test]
fn abs_product_strategy_rejects_missing_and_extra_original_requirements() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(source51("direct"));
        let p = selected51(&mut run);
        match change {
            0 => {
                p.requirement_facts.pop();
            }
            1 => {
                p.proof_of_requirement_facts.pop();
            }
            2 => p.requirement_facts.push(p.requirement_facts[0].clone()),
            _ => {
                p.requirement_facts.clear();
                p.proof_of_requirement_facts.clear();
            }
        }
        assert_eq!(
            compiler.compile_run(&run, "Abs51Count").unwrap_err().route,
            "AbsProductStrategy/Requirements"
        );
    }
}
#[test]
fn abs_product_strategy_rejects_reordered_children_and_input_factors() {
    for both in [false, true] {
        let (mut run, compiler) = super::execute(source51("direct"));
        let p = selected51(&mut run);
        p.proof_of_requirement_facts.swap(0, 1);
        if both {
            p.requirement_facts.swap(0, 1);
        }
        assert_eq!(
            compiler.compile_run(&run, "Abs51Order").unwrap_err().route,
            "AbsProductStrategy/RequirementSubject"
        );
    }
}
#[test]
fn abs_product_strategy_requires_original_requirement_fact_ids() {
    let (mut run, compiler) = super::execute(source51("direct"));
    let p = selected51(&mut run);
    let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut p.requirement_facts[0] else {
        panic!()
    };
    f.fact_id = FactId::new(u64::MAX);
    assert_eq!(
        compiler
            .compile_run(&run, "Abs51RequirementId")
            .unwrap_err()
            .route,
        "AbsProductStrategy/RequirementSubject"
    );
}
#[test]
fn abs_product_strategy_rejects_changed_requirement_subject() {
    let (mut run, compiler) = super::execute(source51("direct"));
    let p = selected51(&mut run);
    let second = match &p.requirement_facts[1] {
        Fact::AtomicFact(AtomicFact::EqualFact(f)) => f.right.clone(),
        _ => panic!(),
    };
    let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut p.requirement_facts[0] else {
        panic!()
    };
    f.right = second;
    assert_eq!(
        compiler
            .compile_run(&run, "Abs51RequirementSubject")
            .unwrap_err()
            .route,
        "AbsProductStrategy/RequirementSubject"
    );
}
#[test]
fn abs_product_strategy_repeated_subjects_keep_distinct_original_ids() {
    let (mut run, compiler) = super::execute(source51("repeated"));
    let p = selected51(&mut run);
    assert_eq!(p.requirement_facts[0].ir(), p.requirement_facts[1].ir());
    assert_ne!(
        p.requirement_facts[0].fact_id(),
        p.requirement_facts[1].fact_id()
    );
    p.proof_of_requirement_facts.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&run, "Abs51RepeatedId")
            .unwrap_err()
            .route,
        "AbsProductStrategy/RequirementSubject"
    );
}
#[test]
fn abs_product_strategy_requires_original_child_citations() {
    let (mut run, compiler) = super::execute(source51("direct"));
    let p = selected51(&mut run);
    change_citation51(&mut p.proof_of_requirement_facts[0], FactId::new(u64::MAX));
    compiler
        .compile_run(&run, "Abs51ForeignCitation")
        .expect_err("the original premise must remain visible");
}
#[test]
fn abs_product_strategy_rejects_future_requirement_citation() {
    let (mut run, compiler) = super::execute(source51("direct"));
    let p = selected51(&mut run);
    let id = p.requirement_facts[1].fact_id();
    change_citation51(&mut p.proof_of_requirement_facts[0], id);
    compiler
        .compile_run(&run, "Abs51FutureRequirement")
        .expect_err("later child is not an earlier producer");
}
#[test]
fn abs_product_strategy_rejects_later_sibling_scope_citation() {
    let (mut run, compiler) =
        super::execute(&format!("{}{}", source51("direct"), source51("reverse")));
    let sibling = super::forall_proof(&run.statement_results[1]);
    let id = sibling.fact.dom_facts[0].fact_id();
    change_citation51(&mut selected51(&mut run).proof_of_requirement_facts[0], id);
    compiler
        .compile_run(&run, "Abs51SiblingCitation")
        .expect_err("later closed sibling cannot supply a factor proof");
}
#[test]
fn abs_product_strategy_requires_both_original_parent_formations() {
    let (mut run, compiler) = super::execute(source51("direct"));
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
    std::mem::swap(&mut wd.left, &mut wd.right);
    compiler
        .compile_run(&run, "Abs51ParentWd")
        .expect_err("each original parent endpoint must be formed");
}
#[test]
fn abs_product_strategy_requires_original_child_absolute_formation() {
    let (mut run, compiler) = super::execute(source51("direct"));
    let p = selected51(&mut run);
    let equal = super::equality_proof_mut(&mut p.proof_of_requirement_facts[0]);
    let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
    std::mem::swap(&mut wd.left, &mut wd.right);
    compiler
        .compile_run(&run, "Abs51ChildWd")
        .expect_err("absProduct must consume original real-argument formation");
}
