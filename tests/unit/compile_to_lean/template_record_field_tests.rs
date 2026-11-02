use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    EqualitySearchProofByObjectDefinition,
    by_fn_application::{EqualitySearchProofByFnApplicationObjectDefinition,
        by_parent_checked_beta::{ByParentCheckedBetaObjectDefinitionProof, ParentCheckedBetaFunctionBody},
        struct_field_value::{StructFieldValueProof, StructTupleValueSource}},
};
use crate::execute::execute_fact_stmt::known_tuple::KnownFunctionTupleApplicability;
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/template_record_function_fields/statement.lit"),
    include_str!("../../../lean/examples/template_record_guarded_fields/statement.lit"),
    include_str!("../../../lean/examples/template_generic_record_fields/statement.lit"),
    include_str!("../../../lean/examples/template_generic_factory_fields/statement.lit"),
];

fn field_value(run: &mut RunLitexCodeResult) -> &mut StructFieldValueProof {
    let fact = super::fact_statement_mut(run.statement_results.last_mut().unwrap());
    let equal = super::equality_proof_mut(&mut fact.verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(
                ByParentCheckedBetaObjectDefinitionProof::OneSide(beta),
            ),
        ),
    ) = &mut equal.searched_proof
    else {
        panic!("field beta")
    };
    let ParentCheckedBetaFunctionBody::StructField(field) = &mut beta.function_body else {
        panic!("field value")
    };
    field
}

#[test]
fn template_record_fields_replay_original_instances_and_generic_factories() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "template_records")
            .expect(source);
        assert_eq!(
            lean,
            compiler.compile_run(&run, "template_records").unwrap()
        );
        assert!(!lean.contains("sorry") && !lean.contains("axiom "));
    }
}

#[test]
fn template_record_fields_require_original_arguments_and_guards() {
    let source = SOURCES[1].replace("\\quotient_box<2>.op(6) = 3", "");
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(&source);
        let fact = super::fact_statement_mut(run.statement_results.last_mut().unwrap());
        let equal = super::equality_proof_mut(&mut fact.verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                    field,
                )),
            ..
        } = equal
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .left
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("template field WD")
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(instance),
            ..
        } = field.child_obj_well_defined[0].as_detailed_mut().unwrap()
        else {
            panic!("instance WD")
        };
        assert_eq!(instance.requirement_fact_verified.len(), 2);
        match mutation {
            0 => {
                instance.requirement_fact_verified.pop();
            }
            1 => instance.requirement_fact_verified.swap(0, 1),
            2 => instance.child_obj_well_defined.clear(),
            3 => super::replace_wd_subject(
                &mut instance.child_obj_well_defined[0],
                super::number_object("0"),
            ),
            4 => field.projection_steps[0]
                .carrier
                .params
                .push(super::number_object("99")),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_template_record_wd")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_record_values_validate_declaration_substitution() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        let field = field_value(&mut run);
        let StructTupleValueSource::Template { instance, value } = &mut field.source else {
            panic!("template tuple source")
        };
        match mutation {
            0 => instance.args.swap(1, 2),
            1 => {
                value.args.pop();
            }
            2 => value.args[1] = Box::new(super::number_object("99")),
            3 => field.carrier.params[0] = Obj::StandardSet(StandardSet::C),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_template_record_value")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_factory_tuple_requires_selected_signature_and_peers() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[3]);
        let field = field_value(&mut run);
        let StructTupleValueSource::Function(source) = &mut field.source else {
            panic!("factory tuple")
        };
        let KnownFunctionTupleApplicability::TemplateDefinition {
            instance,
            signature,
            alternative_template_signatures,
            ..
        } = &mut source.applicability
        else {
            panic!("template applicability")
        };
        match mutation {
            0 => instance.args.clear(),
            1 => signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            2 => alternative_template_signatures.clear(),
            3 => {
                alternative_template_signatures[0].instance.args[0] =
                    Obj::StandardSet(StandardSet::C)
            }
            4 => source.value.args[1] = Box::new(super::number_object("99")),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_template_tuple_source")
            .expect_err(&format!("mutation {mutation}"));
    }
}
