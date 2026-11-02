use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    EqualitySearchProofByObjectDefinition,
    by_fn_application::{EqualitySearchProofByFnApplicationObjectDefinition,
        by_parent_checked_beta::{ByParentCheckedBetaObjectDefinitionProof, ParentCheckedBetaFunctionBody},
        struct_field_value::{StructFieldValueProof, StructTupleValueSource}},
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/nested_returned_record_fields/statement.lit"),
    include_str!("../../../lean/examples/nested_literal_record_fields/statement.lit"),
    include_str!("../../../lean/examples/nested_guarded_record_fields/statement.lit"),
    include_str!("../../../lean/examples/arbitrary_record_function_fields/statement.lit"),
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

fn value_source() -> String {
    SOURCES[0].replace(
        "outer(2).inner.tag $in N\nrelease struct def outer(2)\n",
        "",
    )
}

#[test]
fn nested_record_values_replay_returned_calls_tuples_and_arbitrary_functions() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "nested_records").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "nested_records").unwrap());
        assert!(!lean.contains("sorry") && !lean.contains("axiom "));
    }
}

#[test]
fn nested_record_values_require_the_original_projection_path() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(&value_source());
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
            panic!("nested field WD")
        };
        assert_eq!(field.projection_steps.len(), 2);
        match mutation {
            0 => {
                field.projection_steps.pop();
            }
            1 => field.projection_steps[1].field_index = 0,
            2 => field.projection_steps[1].carrier = field.projection_steps[0].carrier.clone(),
            3 => field.argument_scope = None,
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_nested_projection")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn nested_record_values_require_original_intermediate_application() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(&value_source());
        let field = field_value(&mut run);
        let StructTupleValueSource::ReturnedFunction {
            application_well_defined,
            function,
            ..
        } = &mut field.source
        else {
            panic!("returned function tuple")
        };
        match mutation {
            0 => super::replace_wd_subject(
                &mut field.receiver_well_defined,
                super::number_object("99"),
            ),
            1 => field.index = 1,
            2 => super::replace_wd_subject(application_well_defined, super::number_object("99")),
            3 => {
                function.value.args.pop();
            }
            4 => function.value.args[1] = Box::new(super::number_object("99")),
            5 => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(call),
                    ..
                } = application_well_defined.as_detailed_mut().unwrap()
                else {
                    panic!("call WD")
                };
                call.domain_fn_set = None;
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_nested_return")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn nested_record_values_check_returned_literal_coordinates() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let field = field_value(&mut run);
        let StructTupleValueSource::Returned { value, .. } = &mut field.source else {
            panic!("returned literal tuple")
        };
        match mutation {
            0 => {
                value.args.pop();
            }
            1 => value.args[1] = Box::new(super::number_object("99")),
            2 => field.carrier.params.push(super::number_object("99")),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_nested_literal")
            .expect_err(&format!("mutation {mutation}"));
    }
}
