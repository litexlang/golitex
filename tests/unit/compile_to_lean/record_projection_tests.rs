use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnBodyInReturnSetProof, AnonymousFnObjWellDefinedProof,
    FnObjDomainFnSetEvidence, FunctionSpaceObjWellDefinedProofByDef,
    StructishObjWellDefinedProofByDef,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty as Known,
    InFactSearchProofByKnownSpecialProperty as InKnown,
};
use crate::execute::ExecHaveFnEqualStmtResult;
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# Apply a real function stored in a record.
struct RealMap:
    action fn(x R) R
    marker R

have fn apply_map(m &RealMap, x R) R = m.action(x)

forall m &RealMap, x R:
    apply_map(m, x) = m.action(x)
"#,
    r#"# Apply a function in a nested record, directly and through a reusable wrapper.
struct RealMap:
    action fn(x R) R
    marker R

have fn apply_map(m &RealMap, x R) R = m.action(x)

struct RealBundle:
    inner &RealMap
    base R

have fn apply_bundle(b &RealBundle, x R) R = b.inner.action(x)

forall b &RealBundle, x R:
    b.inner.action(x) $in R

forall b &RealBundle, x R:
    apply_bundle(b, x) = b.inner.action(x)

forall b &RealBundle, x R:
    apply_map(b.inner, x) = b.inner.action(x)
"#,
    r#"# Apply a record function on its nonzero domain.
struct GuardedMap:
    action fn(x R: x != 0) R
    marker R

have fn apply_guarded(m &GuardedMap, x R: x != 0) R = m.action(x)

forall m &GuardedMap, x R:
    x != 0
    =>:
        apply_guarded(m, x) = m.action(x)
"#,
    r#"# Observe a real record function result in the complex numbers.
struct RealMap:
    action fn(x R) R
    marker R

have fn apply_map_complex(m &RealMap, x R) C = m.action(x)
"#,
];

fn formula(run: &mut RunLitexCodeResult, index: usize) -> &mut AnonymousFnObjWellDefinedProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(function),
    )) = &mut run.statement_results[index]
    else {
        panic!("formula declaration")
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                proof,
            )),
        ..
    }) = function
        .anonymous_fn_well_defined
        .as_detailed_success_mut()
        .unwrap()
    else {
        panic!("formula WD")
    };
    proof
}

#[test]
fn record_projection_retains_and_validates_each_original_path_step() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        let body = formula(&mut run, 3);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = body.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("field call")
        };
        if mutation == 7 {
            let Some(FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }) =
                &mut call.domain_fn_set
            else {
                panic!("field signature")
            };
            fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                        field,
                    )),
                ..
            } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
            else {
                panic!("projection WD")
            };
            assert_eq!(field.projection_steps.len(), 2);
            assert_eq!(
                field
                    .projection_steps
                    .iter()
                    .map(|s| s.field_index)
                    .collect::<Vec<_>>(),
                vec![0, 0]
            );
            assert_ne!(
                field.projection_steps[0].carrier,
                field.projection_steps[1].carrier
            );
            match mutation {
                0 => field.projection_steps.clear(),
                1 => {
                    field.projection_steps.pop();
                }
                2 => field.projection_steps.swap(0, 1),
                3 => field.projection_steps[0].field_index = usize::MAX,
                4 => field.projection_steps[0].carrier = field.projection_steps[1].carrier.clone(),
                5 => field.projection_steps[1].field_index = 1,
                6 => field.child_obj_well_defined.clear(),
                _ => unreachable!(),
            }
        }
        compiler
            .compile_run(&run, "bad_record_projection")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn record_projection_requires_field_domain_and_declared_return_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        let body = formula(&mut run, 1);
        if mutation == 0 {
            body.assumed_dom_facts.clear();
        } else if mutation == 1 {
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = body.body_well_defined.as_detailed_mut().unwrap()
            else {
                panic!("guarded field call")
            };
            call.requirement_fact_verified.pop();
        } else {
            let AnonymousFnBodyInReturnSetProof::CheckedMembership(member) =
                &mut body.body_in_ret_set
            else {
                panic!("return member")
            };
            let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(Known::InFact(
                InKnown::FieldApplicationInDeclaredCodomain(proof),
            )) = &mut super::atomic_proof_mut(member).searched_proof
            else {
                panic!("declared field return")
            };
            match mutation {
                2 => proof.declared_signature.dom_facts.clear(),
                3 => proof.applied_return_set = Obj::StandardSet(StandardSet::C),
                _ => proof.declared_signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            }
        }
        compiler
            .compile_run(&run, "bad_field_return")
            .expect_err(&format!("mutation {mutation}"));
    }
}

const GENERIC_SOURCES: &[&str] = &[
    r#"# A binary operation stored in a parameterized record remains closed under repeated application.
struct BinaryOperation<A nonempty_set>:
    zero A
    combine fn(x, y A) A

struct OperationBundle<A nonempty_set>:
    operation &BinaryOperation<A>
    tag N

forall B nonempty_set, b &OperationBundle<B>, x, y B:
    b.operation.combine(x, y) $in B

forall B nonempty_set, b &OperationBundle<B>, x, y B:
    b.operation.combine(b.operation.combine(x, y), x) $in B
"#,
    r#"# A three-level record preserves the carrier of its binary operation.
struct BinaryOperation<A nonempty_set>:
    zero A
    combine fn(x, y A) A

struct OperationBundle<A nonempty_set>:
    operation &BinaryOperation<A>
    tag N

struct NestedBundle<A nonempty_set>:
    bundle &OperationBundle<A>
    tag N

forall B nonempty_set, b &NestedBundle<B>, x, y B:
    b.bundle.operation.combine(x, y) $in B
"#,
    r#"# A binary operation follows a preceding selected point in a parameterized record.
struct BinaryOperation<A nonempty_set>:
    zero A
    combine fn(x, y A) A

struct SelectedOperation<A nonempty_set>:
    point A
    operation &BinaryOperation<A>

forall B nonempty_set, b &SelectedOperation<B>, x, y B:
    b.operation.combine(x, y) $in B
"#,
    r#"# Nested constrained records preserve the domain and range of a binary operation.
struct PointedOperation<A nonempty_set, a A>:
    point A
    combine fn(x, y A) A
    <=>:
        point = a

struct PointedBundle<A nonempty_set, a A>:
    operation &PointedOperation<A, a>
    tag N
    <=>:
        tag = 0

forall B nonempty_set, a B, b &PointedBundle<B, a>, x, y B:
    b.operation.combine(x, y) $in B
"#,
    r#"# Tracer: instantiated function fields retain their actual parameter domains.
# Before: the named theorem failed WD with an undefined definition parameter A.
# struct ProbeOp<A nonempty_set>:
#     zero A
#     add fn(x, y A) A
# thm generic_reflexive:
#     ? forall B nonempty_set, s &ProbeOp<B>, x, y B:
#         s.add(x, y) = s.add(x, y)
# Now: the same theorem and its concrete/nested forms verify.
# Boundary: wrong argument types, missing guards and false laws still fail.
# Run: target/release/litex -strict -f examples/wd/struct_field_instantiation.lit

struct ProbeOp<A nonempty_set>:
    zero A
    add fn(x, y A) A

thm generic_reflexive:
    ? forall B nonempty_set, s &ProbeOp<B>, x, y B:
        s.add(x, y) = s.add(x, y)

thm real_reflexive:
    ? forall s &ProbeOp<R>, x, y R:
        s.add(x, y) = s.add(x, y)

struct NestedOp<A nonempty_set>:
    operation &ProbeOp<A>
    tag N

thm nested_reflexive:
    ? forall B nonempty_set, s &NestedOp<B>, x, y B:
        s.operation.add(x, y) = s.operation.add(x, y)

struct PointEvaluator<A nonempty_set, point A>:
    tag N
    at fn(x {point}) A

thm dependent_field_reflexive:
    ? forall B nonempty_set, point B, s &PointEvaluator<B, point>:
        s.at(point) = s.at(point)

claim:
    ? forall s &ProbeOp<R>:
        s.add(0, 1) = s.add(0, 1)
    by thm real_reflexive(s, 0, 1) => s.add(0, 1) = s.add(0, 1)
"#,
];

#[test]
fn record_projection_rejects_changed_intermediate_header_and_declaration_wd() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(GENERIC_SOURCES[0]);
        if mutation < 3 {
            let forall = super::forall_proof_mut(&mut run.statement_results[2]);
            let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
            let wd = &mut atomic
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter[0];
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = wd.as_detailed_mut().unwrap()
            else {
                panic!("field call")
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(
                        field,
                    )),
                ..
            } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
            else {
                panic!("field projection")
            };
            match mutation {
                0 => field.projection_steps[1].carrier.params.clear(),
                1 => field.projection_steps[1].carrier.params[0] = Obj::StandardSet(StandardSet::R),
                _ => field.projection_steps[1].field_index = 0,
            }
        } else {
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
                crate::execute::ExecDefStructStmtResult::Success(declaration),
            )) = &mut run.statement_results[1]
            else {
                panic!("outer declaration")
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(
                        wd,
                    )),
                ..
            } = declaration.field_scope.fields[0]
                .well_defined
                .as_detailed_mut()
                .unwrap()
            else {
                panic!("original field constructor")
            };
            match mutation {
                3 => wd.requirement_fact_verified.clear(),
                4 => wd.child_obj_well_defined.clear(),
                _ => super::replace_wd_subject(
                    &mut wd.child_obj_well_defined[0],
                    Obj::StandardSet(StandardSet::R),
                ),
            }
        }
        compiler
            .compile_run(&run, "bad_generic_field")
            .expect_err(&format!("mutation {mutation}"));
    }
}
