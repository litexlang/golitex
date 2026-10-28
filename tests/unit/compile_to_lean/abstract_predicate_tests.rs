use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferNormalAtomicFactResult, InferNormalAtomicParamTypesProjectedResult,
    InferResult,
};

const TRANSPORT: &str =
    include_str!("../../../lean/examples/abstract_property_transport/statement.lit");

fn conclusion(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    super::atomic_proof_mut(
        &mut super::forall_proof_mut(&mut run.statement_results[1]).proved_then_facts[0]
            .verify_result,
    )
}

#[test]
fn abstract_predicate_examples_replay_deterministically() {
    for source in [
        TRANSPORT,
        include_str!("../../../lean/examples/abstract_relation_transport/statement.lit"),
        include_str!("../../../lean/examples/abstract_function_guard/statement.lit"),
        include_str!("../../../lean/examples/abstract_proposition_identity/statement.lit"),
        include_str!("../../../lean/examples/abstract_property_context/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "abstract_predicates").unwrap();
        assert_eq!(
            lean,
            compiler.compile_run(&run, "abstract_predicates").unwrap()
        );
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn abstract_predicate_signature_kind_name_and_arity_are_checked() {
    for change in 0..4 {
        let (mut run, compiler) = super::execute(TRANSPORT);
        let signature = &mut conclusion(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .predicate_signature;
        let PredicateSignatureWellDefinedProof::AbstractProp { predicate, arity } = signature
        else {
            panic!("actual abstract signature")
        };
        match change {
            0 => *arity += 1,
            1 => {
                *predicate = AtomicName::Plain {
                    name: "unrelated".into(),
                }
            }
            2 => {
                *signature = PredicateSignatureWellDefinedProof::Prop {
                    predicate: predicate.clone(),
                    arity: *arity,
                }
            }
            3 => *signature = PredicateSignatureWellDefinedProof::Builtin,
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "changed_signature").is_err());
    }
}

#[test]
fn abstract_predicate_requires_its_preceding_declaration() {
    for future in [false, true] {
        let (mut run, compiler) = super::execute(TRANSPORT);
        if future {
            run.statement_results.swap(0, 1);
        } else {
            run.statement_results.remove(0);
        }
        assert!(compiler.compile_run(&run, "missing_declaration").is_err());
    }
}

#[test]
fn abstract_predicate_preserves_argument_wd() {
    let (mut run, compiler) = super::execute(TRANSPORT);
    conclusion(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter
        .clear();
    assert!(compiler.compile_run(&run, "missing_argument_wd").is_err());
}

#[test]
fn abstract_predicate_cannot_invent_definition_inferences() {
    let (mut run, compiler) = super::execute(TRANSPORT);
    let infer = &mut super::forall_proof_mut(&mut run.statement_results[1]).proved_then_facts[0]
        .store_and_infer
        .infer;
    let Some(InferResult::AtomicFact(InferAtomicFactResult::NormalAtomicFact(rules))) = infer
    else {
        panic!("actual empty predicate inference")
    };
    assert!(rules.is_empty());
    rules.push(InferNormalAtomicFactResult::ParamTypes(
        InferNormalAtomicParamTypesProjectedResult {
            derived: Vec::new(),
        },
    ));
    assert_eq!(
        compiler
            .compile_run(&run, "invented_inference")
            .unwrap_err()
            .route,
        "AbstractProp/UnexpectedInference"
    );
}

#[test]
fn an_abstract_header_proves_neither_truth_nor_negation() {
    for tail in [
        "$marked(0)",
        "not $marked(0)",
        "$marked(0, 1)",
        "$marked(missing)",
    ] {
        let source = format!("abstract_prop marked(x)\n{tail}\n");
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        let run = runtime.run_litex_code(&source).unwrap();
        assert!(!run.success);
        assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_abstract_use")
            .is_err());
    }
}

#[test]
fn local_abstract_declarations_do_not_escape_their_scope() {
    let source = "sketch:\n    abstract_prop local_opaque(x)\n    forall x R:\n        $local_opaque(x)\n        =>:\n            $local_opaque(x)\n";
    let (run, compiler) = super::execute(source);
    assert_eq!(
        compiler
            .compile_run(&run, "local_abstract")
            .unwrap_err()
            .route,
        "AbstractProp/LocalDeclaration"
    );
}
