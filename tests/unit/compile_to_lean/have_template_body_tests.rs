use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::{
    ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult, ExecHaveObjByExistFactsStmtResult,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# Choose an element of each nonempty set and retain its membership.
template<S nonempty_set>:
    have selected_member S

\selected_member<R> $in R
forall S nonempty_set:
    \selected_member<S> $in S
"#,
    r#"# Choosing from a singleton defines the identity function.
template<a R>:
    have singleton_choice {a}

\singleton_choice<2> = 2

thm singleton_is_real:
    ? forall a R:
        \singleton_choice<a> $in R
    \singleton_choice<a> $in {a}

have fn choose_singleton(a R) R = \singleton_choice<a>

thm singleton_choice_value:
    ? forall a R:
        choose_singleton(a) = a
    \singleton_choice<a> $in {a}
    choose_singleton(a) = \singleton_choice<a> = a

choose_singleton(3) = 3
"#,
    r#"# A function chosen between nonempty sets can be called and composed.
template<A, B nonempty_set>:
    have selected_function fn(x A) B

\selected_function<R, R> $in fn(x R) R
\selected_function<R, R>(2) $in R

have fn chosen_real_value(a R) R = \selected_function<R, R>(a)

chosen_real_value(2) = \selected_function<R, R>(2)
forall a R:
    chosen_real_value(a) = \selected_function<R, R>(a)
"#,
    r#"# Choose a larger real for every input and retain that inequality through a function.
template<a R>:
    have larger R:
        larger > a

\larger<2> $in R
\larger<2> > 2

have fn larger_value(a R) R = \larger<a>
larger_value(2) > 2

thm larger_value_grows:
    ? forall a R:
        larger_value(a) > a
    \larger<a> $in R
    \larger<a> > a
    larger_value(a) = \larger<a>
"#,
];

fn template(run: &mut RunLitexCodeResult) -> &mut ExecDefTemplateStmtSuccessResult {
    match &mut run.statement_results[0] {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
            ExecDefTemplateStmtResult::Success(p),
        )) => p,
        _ => panic!("checked template"),
    }
}

#[test]
fn have_template_members_require_nonempty_evidence_and_exact_ordered_stores() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(body),
            ),
        )) = p.body.as_mut()
        else {
            panic!("nonempty member declaration")
        };
        match mutation {
            0 => body.groups.clear(),
            1 => body.groups[0].nonempty_check = ParamTypeFactCheckResult::Set,
            2 => body.groups[0].defined_params.stored_fact_ids.clear(),
            3 => body.groups[0].param_type_well_defined = ParamTypeWellDefinedProof::Set,
            4 => p.definition_facts[0].source_fact_id = FactId::new(u64::MAX),
            5 => p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_member")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn have_template_existence_keeps_its_source_predicate_and_formation() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[3]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjByExistFacts(
                ExecHaveObjByExistFactsStmtResult::Success(body),
            ),
        )) = p.body.as_mut()
        else {
            panic!("have by existence")
        };
        match mutation {
            0 => {
                let ExistShapedFact::Exist(fact) = &mut body.verify_exist.fact else {
                    panic!()
                };
                fact.facts.clear();
            }
            1 => body
                .verify_exist
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .assumed_body_facts
                .clear(),
            2 => body
                .store_and_infer_result
                .store_and_infer_results
                .swap(0, 1),
            3 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_existence")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_call_from_declared_carrier_replays_instance_and_argument_wd() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = super::fact_statement_mut(&mut run.statement_results[2]);
        let p = super::atomic_proof_mut(&mut p.verify_result);
        let wd = &mut p
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0];
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = wd.as_detailed_mut().unwrap()
        else {
            panic!("call WD")
        };
        let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) =
            &mut call.domain_fn_set
        else {
            panic!("checked template declaration route")
        };
        let signature = fn_set.clone();
        assert_eq!(
            call.child_obj_well_defined.len(),
            2,
            "template declaration route retains the instance and argument WD"
        );
        match mutation {
            0 => {
                call.domain_fn_set = Some(FnObjDomainFnSetEvidence::InFunctionSet {
                    fn_set: signature,
                    fact_id: FactId::new(u64::MAX),
                    function_equal: KnownEqualityPathProof::new(Vec::new()),
                })
            }
            1 => fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::N)),
            2 => call.child_obj_well_defined.clear(),
            3 => call.requirement_fact_verified.clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_call")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn function_valued_alias_template_declares_the_called_signature() {
    let source =
        "template<T set>:\n    have identity fn(x T) T = fn(x T) T {x}\n\\identity<R>(1) $in R";
    let (mut run, compiler) = super::execute(source);
    let declaration = template(&mut run);
    let binding = declaration.statement.template_def_stmt.defined_bindings()[0];
    let name = format!("_template_signature_i{}", binding.id.value());
    let output = compiler.compile_run(&run, "FunctionValuedAlias").unwrap();
    let definition = output
        .find(&format!("noncomputable def {name}"))
        .expect("the referenced signature must be declared for value aliases too");
    let application = output.find("(Litex.call ").expect("checked call");
    assert!(definition < application, "signature must precede its use");
}

#[test]
fn have_template_publication_requires_its_original_visible_prefix() {
    let (mut run, compiler) = super::execute(SOURCES[0]);
    compiler.compile_run(&run, "baseline").unwrap();
    let id = template(&mut run).definition_facts[0]
        .store_and_infer
        .primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(before.visible_template_publication(id).is_none());
    assert!(after.visible_template_publication(id).is_some());
}
