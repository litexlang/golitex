use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# A returned record carries a function and a numeric tag; evaluate both fields.
struct Box:
    op fn(x R) R
    tag N

forall f fn(x R) R:
    (f, 0) $in &Box

have fn make(a R) &Box = (fn(x R) R {x + a}, 0)
make(2).op(3) = 5
make(2).tag = 0
"#,
    r#"# A nonzero parameter remains required when projecting a function from a returned record.
struct Box:
    op fn(x R) R
    tag N

forall f fn(x R) R:
    (f, 0) $in &Box

have fn divide_box(a R: a != 0) &Box = (fn(x R) R {x / a}, 0)

divide_box(2).op(6) = 3

divide_box(2).tag = 0
"#,
];

#[test]
fn returned_record_fields_require_the_original_call_and_projection_stages() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let fact = super::fact_statement_mut(run.statement_results.last_mut().unwrap());
        let equality = super::equality_proof_mut(&mut fact.verify_result);
        let wd = &mut equality.well_defined_proof.as_detailed_mut().unwrap().left;
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                    field,
                )),
            ..
        } = wd.as_detailed_mut().unwrap()
        else {
            panic!("field WD")
        };
        assert_eq!(field.requirement_fact_verified.len(), 2);
        match mutation {
            0 => field.argument_scope = None,
            1 => {
                field.requirement_fact_verified.pop();
            }
            2 => field.requirement_fact_verified.swap(0, 1),
            3 => {
                field.child_obj_well_defined.pop();
            }
            4 => super::replace_wd_subject(
                &mut field.child_obj_well_defined[0],
                super::number_object("99"),
            ),
            5 => field.projection_steps[0].field_index = 0,
            6 => field.projection_steps.clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_returned_record")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn returned_record_fields_validate_the_selected_tuple_and_coordinate() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        EqualitySearchProofByObjectDefinition,
        by_fn_application::{EqualitySearchProofByFnApplicationObjectDefinition,
            by_parent_checked_beta::{ByParentCheckedBetaObjectDefinitionProof, ParentCheckedBetaFunctionBody},
            struct_field_value::StructTupleValueSource},
    };
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        let fact = super::fact_statement_mut(run.statement_results.last_mut().unwrap());
        let equality = super::equality_proof_mut(&mut fact.verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(
                    ByParentCheckedBetaObjectDefinitionProof::OneSide(beta),
                ),
            ),
        ) = &mut equality.searched_proof
        else {
            panic!("field beta")
        };
        let ParentCheckedBetaFunctionBody::StructField(field) = &mut beta.function_body else {
            panic!("field value")
        };
        match mutation {
            0 => field.index = 1,
            1 => super::replace_wd_subject(
                &mut field.receiver_well_defined,
                super::number_object("99"),
            ),
            2 | 3 => {
                let StructTupleValueSource::Function(source) = &mut field.source else {
                    panic!("returned tuple")
                };
                if mutation == 2 {
                    source.value.args.pop();
                } else {
                    source.value.args[1] = Box::new(super::number_object("99"));
                }
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_returned_record_value")
            .expect_err(&format!("mutation {mutation}"));
    }
}
