use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::fn_sets_alpha_equal;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::*;
use crate::execute::{
    ExecDefTemplateStmtResult, ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnEqualStmtResult,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# Compose a nonzero real input with a uniquely specified scalar function.
thm unique_scalar:
    ? forall a R:
        exist! x R st {x = a}
    witness exist! x R st {x = a} from a

template<a R: a != 0,>:
    have fn selected_scalar by exist!:
        ? forall index R:
            index != 0
            =>:
                exist! x R st {x = a}

have fn selected_again(a R: a != 0) R = \selected_scalar<a>(3)

selected_again(2) = \selected_scalar<2>(3) = 2

forall a R:
    a != 0
    =>:
        selected_again(a) = \selected_scalar<a>(3) = a
"#,
    r#"# Use the real output of a uniquely specified function as a complex value.
thm unique_scalar:
    ? forall a R:
        exist! x R st {x = a}
    witness exist! x R st {x = a} from a

template<a R: a != 0,>:
    have fn selected_scalar by exist!:
        ? forall index R:
            index != 0
            =>:
                exist! x R st {x = a}

have fn selected_complex(a R: a != 0) C = \selected_scalar<a>(3)

selected_complex(2) = \selected_scalar<2>(3) = 2
"#,
    r#"# Select a record field through a uniquely specified function.
struct Point<K nonempty_set, S nonempty_set>:
    value S
    tag N

thm unique_value:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>:
        exist! x S st {x = t.value}
    witness exist! x S st {x = t.value} from t.value

template<K nonempty_set, S nonempty_set, t &Point<K, S>>:
    have fn selected_value by exist!:
        ? forall index N:
            exist! x S st {x = t.value}

thm selected_value_spec:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>:
        \selected_value<K, S, t>(0) = t.value

struct Unary<S nonempty_set>:
    call fn(x S) S
    tag N

# The template occurs under another call, whose WD uses read-only premises.
thm selected_value_nested:
    ? forall K nonempty_set, S nonempty_set, t &Point<K, S>, op &Unary<S>:
        op.call(\selected_value<K, S, t>(0)) $in S

have fn chosen_field(p &Point<R, R>) R = \selected_value<R, R, p>(0)

forall p &Point<R, R>:
    chosen_field(p) = \selected_value<R, R, p>(0) = p.value
"#,
    r#"# Compose a uniquely specified two-input sum with fixed arguments.
thm unique_sum:
    ? forall a, x, y R:
        exist! z R st {z = a + x + y}
    witness exist! z R st {z = a + x + y} from a + x + y

template<a R>:
    have fn selected_sum by exist!:
        ? forall x, y R:
            exist! z R st {z = a + x + y}

have fn chosen_sum(a R) R = \selected_sum<a>(1, 2)

chosen_sum(3) = \selected_sum<3>(1, 2) = 6

forall a R:
    chosen_sum(a) = \selected_sum<a>(1, 2) = a + 1 + 2
"#,
];

fn formula(run: &mut RunLitexCodeResult) -> &mut AnonymousFnObjWellDefinedProof {
    let p = run
        .statement_results
        .iter_mut()
        .find_map(|s| match s {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
                ExecHaveFnEqualStmtResult::Success(p),
            )) => Some(p),
            _ => None,
        })
        .unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                p,
            )),
        ..
    } = p
        .anonymous_fn_well_defined
        .as_detailed_success_mut()
        .unwrap()
        .unwrap()
    else {
        panic!()
    };
    p
}

fn template(run: &mut RunLitexCodeResult) -> &mut crate::execute::ExecDefTemplateStmtSuccessResult {
    run.statement_results
        .iter_mut()
        .find_map(|s| match s {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
                ExecDefTemplateStmtResult::Success(p),
            )) => Some(p),
            _ => None,
        })
        .unwrap()
}

#[test]
fn template_guard_fact_identity_does_not_change_its_function_signature() {
    let (mut run, compiler) = super::execute(SOURCES[0]);
    compiler.compile_run(&run, "before").unwrap();
    let p = formula(&mut run);
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = p.body_well_defined.as_detailed_mut().unwrap()
    else {
        panic!()
    };
    let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) = &mut call.domain_fn_set
    else {
        panic!()
    };
    let original = fn_set.clone();
    let QuantifierFreeFact::AtomicFact(AtomicFact::NotEqualFact(guard)) = &mut fn_set.dom_facts[0]
    else {
        panic!()
    };
    guard.fact_id = FactId::new(u64::MAX);
    assert_ne!(*fn_set, original);
    assert!(fn_sets_alpha_equal(fn_set, &original));
    compiler.compile_run(&run, "after").unwrap();
}

#[test]
fn selected_template_composition_requires_exact_call_wd_and_guard_evidence() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = formula(&mut run);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = p.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) =
            &mut call.domain_fn_set
        else {
            panic!()
        };
        match mutation {
            0 => fn_set.dom_facts.clear(),
            1 => fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::N)),
            2 => {
                fn_set.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            3 => {
                call.requirement_fact_verified.pop();
            }
            4 => call.requirement_fact_verified.swap(0, 1),
            5 => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(instance),
                    ..
                } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                instance.requirement_fact_verified.pop();
            }
            6 => call.child_obj_well_defined.swap(0, 1),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_call")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn selected_template_callee_requires_original_property_formation_and_publication() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[3]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            ExecHaveFnByForallExistUniqueStmtResult::Success(body),
        )) = p.body.as_mut()
        else {
            panic!()
        };
        let FactWellDefinedProof::ForallFact(wd) = &mut body.property_well_defined else {
            panic!()
        };
        match mutation {
            0 => wd.as_detailed_mut().unwrap().then.clear(),
            1 => wd
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            2 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            3 => {
                let StoreFactResult::ForallFact(stored) =
                    &mut p.definition_facts[1].store_and_infer.store
                else {
                    panic!()
                };
                stored.fact.typed_parameters.groups.swap(0, 1);
            }
            4 => p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_publication")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_constructor_publication_is_visible_only_after_its_declaration() {
    let (run, compiler) = super::execute(SOURCES[3]);
    compiler.compile_run(&run, "baseline").unwrap();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(p),
    )) = &run.statement_results[1]
    else {
        panic!()
    };
    let id = p.definition_facts[1].store_and_infer.primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let after = SourcePosition {
        before: 2,
        ..before
    };
    assert!(before.visible_template_publication(id).is_none());
    assert!(after.visible_template_publication(id).is_some());
}
