use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty as Known,
    InFactSearchProofByKnownSpecialProperty as InKnown,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::StructishObjWellDefinedProofByDef;
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# A selected point fixes the input domain of an operation stored in a later record field.
struct AnchoredOperation<A nonempty_set, a A>:
    point A
    combine fn(x {a}, y A) A

struct AnchoredBundle<A nonempty_set>:
    point A
    operation &AnchoredOperation<A, point>

forall B nonempty_set, b &AnchoredBundle<B>, y B:
    b.operation.combine(b.point, y) $in B
"#,
    r#"# A later record field uses the selected point; its value retains and transports its carrier.
struct SelectedPoint<A nonempty_set, a A>:
    value A
    tag N
    <=>:
        value = a

struct SelectedBox<A nonempty_set>:
    point A
    selected &SelectedPoint<A, point>

forall B nonempty_set, b &SelectedBox<B>:
    b.selected.value $in B

forall B, D nonempty_set, b &SelectedBox<B>:
    B = D
    =>:
        b.selected.value $in D
"#,
    r#"# A dependent record contains another dependent record whose coordinates lie in successive singleton sets.
struct PointFiber<A nonempty_set, a A>:
    base {a}
    copy {base}

struct FiberBox<A nonempty_set>:
    point A
    fiber &PointFiber<A, point>

forall B nonempty_set, b &FiberBox<B>:
    b.fiber.base $in {b.point}
    b.fiber.copy $in {b.fiber.base}
"#,
    r#"# A third record field is indexed by a value projected from the second field.
struct SelectedPoint<A nonempty_set, a A>:
    value A
    tag N
    <=>:
        value = a

struct PointFiber<A nonempty_set, a A>:
    base {a}
    copy {base}

struct ChainedSelection<A nonempty_set>:
    point A
    selected &SelectedPoint<A, point>
    fiber &PointFiber<A, selected.value>

forall B nonempty_set, b &ChainedSelection<B>:
    b.fiber.base $in {b.selected.value}
    b.fiber.copy $in {b.fiber.base}
"#,
];

#[test]
fn dependent_record_carriers_require_original_instantiation_wd() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
            crate::execute::ExecDefStructStmtResult::Success(declaration),
        )) = &mut run.statement_results[1]
        else {
            panic!("dependent structure")
        };
        let wd = &mut declaration.field_scope.fields[1].well_defined;
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(proof)),
            ..
        } = wd.as_detailed_mut().unwrap()
        else {
            panic!("original field instantiation")
        };
        assert_eq!(proof.requirement_fact_verified.len(), 2);
        match mutation {
            0 => {
                proof.requirement_fact_verified.pop();
            }
            1 => proof.requirement_fact_verified.swap(0, 1),
            2 => {
                proof.child_obj_well_defined.pop();
            }
            _ => super::replace_wd_subject(
                &mut proof.child_obj_well_defined[1],
                Obj::StandardSet(StandardSet::R),
            ),
        }
        compiler
            .compile_run(&run, "bad_dependent_field_wd")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn dependent_record_membership_validates_declared_set_and_original_equality() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let forall =
            super::forall_proof_mut(&mut run.statement_results[if mutation == 1 { 3 } else { 2 }]);
        let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        if mutation <= 1 {
            let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(Known::InFact(
                InKnown::FieldInDeclaredSet(proof),
            )) = &mut atomic.searched_proof
            else {
                panic!("declared field membership")
            };
            if mutation == 0 {
                proof.declared_set = Obj::StandardSet(StandardSet::C);
            } else {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) = &mut proof.set_match
                else {
                    panic!("recorded carrier transport")
                };
                assert!(!path.path.is_empty());
                path.path.clear();
            }
        } else {
            let wd = &mut atomic
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter[0];
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                        proof,
                    )),
                ..
            } = wd.as_detailed_mut().unwrap()
            else {
                panic!("nested projection WD")
            };
            if mutation == 2 {
                proof.projection_steps.swap(0, 1);
            } else {
                proof.projection_steps[1].carrier.params.pop();
            }
        }
        compiler
            .compile_run(&run, "bad_declared_field_member")
            .expect_err(&format!("mutation {mutation}"));
    }
}
