use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{AtomicExceptEqualityFactSearchProofByDefinition as Definition,BuiltinPropDefinitionProof as Builtin};
use crate::prelude::*;

const SOURCE: &str =
    include_str!("../../../lean/examples/dvd_definition_from_certificates/statement.lit");

#[test]
fn dvd_definition_replays_both_original_certificates() {
    let (mut run, compiler) = super::execute(SOURCE);
    let proof = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let AtomicExceptEqualityFactSearchedProof::ByDefinition(Definition::BuiltinProp(Builtin::Dvd(
        p,
    ))) = &proof.searched_proof
    else {
        panic!("selected Dvd definition")
    };
    assert_eq!(
        (
            p.requirement_facts.len(),
            p.proof_of_requirement_facts.len()
        ),
        (2, 2)
    );
    let output = compiler
        .compile_run(&run, "dvd_definition")
        .unwrap_or_else(|e| panic!("{e}"));
    assert!(output.contains("Litex.dvdFromRemainderAndMultiple"));
    assert!(output.contains("Litex.integerMultipleFromZeroRemainder"));
    assert_eq!(
        output,
        compiler.compile_run(&run, "dvd_definition").unwrap()
    );
}

#[test]
fn dvd_definition_requires_both_ordered_original_proofs_and_multiple_binder() {
    for change in ["missing", "order", "remainder", "binder"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let proof = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByDefinition(Definition::BuiltinProp(
            Builtin::Dvd(p),
        )) = &mut proof.searched_proof
        else {
            panic!()
        };
        match change {
            "missing" => {
                p.proof_of_requirement_facts.pop();
            }
            "order" => p.proof_of_requirement_facts.swap(0, 1),
            "remainder" => {
                let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut p.requirement_facts[0] else {
                    panic!()
                };
                f.right = Obj::Literal(Literal::Number(Number::new("1".into())));
            }
            "binder" => {
                let Fact::ExistFact(f) = &mut p.requirement_facts[1] else {
                    panic!()
                };
                f.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX);
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("retain exact zero remainder and multiple certificates");
    }
}
