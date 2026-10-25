use crate::prelude::*;

const REPEATED: &str =
    include_str!("../../../lean/examples/repeated_coordinate_fields/statement.lit");
const ELEMENT: &str = include_str!("../../../lean/examples/member_coordinate_pairs/statement.lit");

#[test]
fn dependent_struct_fields_replay_original_membership_and_release() {
    for source in [
        REPEATED,
        ELEMENT,
        include_str!("../../../lean/examples/repeated_coordinate_triples/statement.lit"),
        include_str!("../../../lean/examples/positive_repeated_coordinates/statement.lit"),
        include_str!("../../../lean/examples/equal_coordinates_membership/statement.lit"),
        include_str!("../../../lean/examples/reciprocal_coordinate_fields/statement.lit"),
        include_str!("../../../lean/examples/chosen_repeated_coordinates/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "dependent_fields")
            .unwrap_or_else(|e| panic!("{}: {e:?}", source.lines().next().unwrap()));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "dependent_fields").unwrap()
        );
        assert!(lean.contains("Litex.IndexedUnionSemantics M"));
        assert!(
            lean.contains("Litex.inDependentCartAt") || lean.contains("Litex.inDependentCart_iff")
        );
        assert!(!lean.contains("axiom ") && !lean.contains("sorry"));
    }
}

#[test]
fn dependent_struct_field_and_release_facts_keep_original_scope() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(REPEATED);
    let p = declaration(&mut run);
    let header = SourcePosition::new(None, SourceOwner::StructHeader(p), usize::MAX);
    let mut private_facts = Vec::new();
    for (index, stage) in p.field_scope.fields.iter().enumerate() {
        let id = stage.defined.store_and_infer_results[0].primary_fact_id();
        private_facts.push(id);
        let prior = SourcePosition::new(Some(&header), SourceOwner::StructFields(p), index);
        let completed = SourcePosition {
            before: index + 1,
            ..prior
        };
        assert!(prior.visible_fact(id, &compiler.runtime).is_err());
        assert!(completed.visible_fact(id, &compiler.runtime).is_ok());
    }
    let proof = super::forall_proof_mut(&mut run.statement_results[3]);
    let header = SourcePosition::new(None, SourceOwner::Forall(proof), 1);
    let layer = &proof
        .introduced_params
        .auto_opened_struct_layers
        .as_ref()
        .unwrap()[0];
    for (index, store) in layer.store_and_infer.iter().enumerate() {
        let id = store.primary_fact_id();
        private_facts.push(id);
        let prior = SourcePosition::new(Some(&header), SourceOwner::StructLayer(layer), index);
        let completed = SourcePosition {
            before: index + 1,
            ..prior
        };
        assert!(prior.visible_fact(id, &compiler.runtime).is_err());
        assert!(completed.visible_fact(id, &compiler.runtime).is_ok());
    }
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    for id in private_facts {
        assert!(outside.visible_fact(id, &compiler.runtime).is_err());
    }
}

#[test]
fn dependent_field_inference_constructors_follow_the_field_prefix() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/reciprocal_coordinate_fields/statement.lit"
    ));
    let p = declaration(&mut run);
    let header = SourcePosition::new(None, SourceOwner::StructHeader(p), usize::MAX);
    let before = SourcePosition::new(Some(&header), SourceOwner::StructFields(p), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    let zero = super::number_object("0");
    assert!(before
        .with_visible_inferred_subject(&zero, &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    assert!(compiler.compile_object_reference(&zero, &before).is_err());
    assert!(after
        .with_visible_inferred_subject(&zero, &mut |_, _| Ok(()))
        .unwrap()
        .is_some());
    assert!(compiler.compile_object_reference(&zero, &after).is_ok());
    let field = Obj::Identifier(IdentifierObj::from_bound_name(
        &p.statement.fields[0].binding,
    ));
    assert!(compiler.compile_object_reference(&field, &after).is_ok());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    // Closed numeric leaves can be reused; the field and its hypotheses cannot escape.
    assert!(compiler.compile_object_reference(&zero, &outside).is_ok());
    assert!(compiler.compile_object_reference(&field, &outside).is_err());
}

fn declaration(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::ExecDefStructStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
        crate::execute::ExecDefStructStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("struct")
    };
    p
}

#[test]
fn dependent_struct_field_formation_rejects_missing_reordered_and_forward_evidence() {
    for change in 0..5 {
        let (mut run, compiler) = super::execute(REPEATED);
        let p = declaration(&mut run);
        match change {
            0 => p.field_scope.fields.swap(0, 1),
            1 => {
                p.field_scope.fields.pop();
            }
            2 => p.field_scope.fields[0]
                .defined
                .store_and_infer_results
                .clear(),
            3 => {
                p.statement.fields[0].field_type = Obj::Identifier(IdentifierObj::from_bound_name(
                    &p.statement.fields[1].binding,
                ))
            }
            4 => {
                p.statement.fields[1].field_type = Obj::Identifier(IdentifierObj::from_bound_name(
                    &p.statement.fields[1].binding,
                ))
            }
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "invalid_dependent_fields")
            .is_err());
    }
}

#[test]
fn dependent_struct_membership_requires_instantiated_field_types() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for change in 0..2 {
        let (mut run, compiler) = super::execute(REPEATED);
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[2]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::StructObjMembership(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!("membership")
        };
        if change == 0 {
            p.carrier_obligations.pop();
        } else {
            p.carrier_obligations.swap(0, 1);
        }
        assert!(compiler
            .compile_run(&run, "invalid_dependent_member")
            .is_err());
    }
}

#[test]
fn dependent_struct_release_cannot_replace_a_dependent_carrier() {
    for index in [0, 4] {
        let (mut run, compiler) = super::execute(REPEATED);
        let layers = super::forall_proof_mut(&mut run.statement_results[3])
            .introduced_params
            .auto_opened_struct_layers
            .as_mut()
            .unwrap();
        let StoreFactResult::AtomicFact(stored) = &mut layers[0].store_and_infer[index].store
        else {
            panic!("atomic release")
        };
        let AtomicFact::InFact(f) = &mut stored.fact else {
            panic!("member")
        };
        if index == 0 {
            let Obj::ProductShape(ProductShape::Cart(c)) = &mut f.set else {
                panic!("cart")
            };
            c.args[1] = Box::new(Obj::StandardSet(StandardSet::R));
        } else {
            f.set = Obj::StandardSet(StandardSet::R);
        }
        assert!(compiler
            .compile_run(&run, "invalid_dependent_release")
            .is_err());
    }
}

#[test]
fn dependent_struct_fields_cannot_accept_unequal_singleton_coordinates() {
    let source = "struct RepeatedCoordinate:\n    x R\n    y {x}\n1 $in {1}\n(1, 2) $in &RepeatedCoordinate\n";
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success);
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "invalid_dependent_tuple")
        .is_err());
}

#[test]
fn dependent_nonliteral_membership_requires_original_shape_and_coordinates() {
    use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
    use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    let source = include_str!("../../../lean/examples/equal_coordinates_membership/statement.lit");
    for change in 0..4 {
        let (mut run, compiler) = super::execute(source);
        let atomic = super::atomic_proof_mut(
            &mut super::forall_proof_mut(&mut run.statement_results[1]).proved_then_facts[1]
                .verify_result,
        );
        let own_id = atomic.fact.fact_id();
        let (domain, coordinates) = match &mut atomic.searched_proof {
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                    InFactSearchProofByBuiltinRule::CartMembership(p),
                ),
            ) => (&mut p.domain, &mut p.proof_of_requirement_facts),
            AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartMembership(p),
            ) => (&mut p.domain, &mut p.proof_of_requirement_facts),
            _ => panic!("recorded Cartesian membership"),
        };
        match change {
            0 => {
                coordinates.pop();
            }
            1 => coordinates.swap(1, 2),
            2 | 3 => {
                let CompleteFunctionDomainSourceProof::FiniteFunction(finite) =
                    &mut domain.source.source
                else {
                    panic!("finite domain")
                };
                let KnownTupleShapeProof::CartesianMembership(shape) = &mut finite.source else {
                    panic!("original membership")
                };
                if change == 2 {
                    shape.membership.fact_id = own_id;
                } else {
                    shape.membership.element = shape.membership.set.clone();
                }
            }
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "invalid_dependent_cart")
            .is_err());
    }
}
