use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    VerifyForallFactProof, VerifyForallFactResult,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::{ExecFactStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

const SOURCE: &str =
    include_str!("../../../../examples/proof_nodes/forall/known_source_nested_unique.lit");

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}
fn parse(rt: &mut Runtime, code: &str) -> crate::ast::fact::ForallFact {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::ForallFact(fact)) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("forall");
    };
    fact
}
fn prefix() -> &'static str {
    SOURCE.rsplit_once("\nforall ").unwrap().0
}
fn sizes(rt: &Runtime) -> Vec<(usize, usize)> {
    rt.execution_environments_stack
        .iter()
        .map(|env| {
            (
                env.facts.facts_by_id.len(),
                env.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect()
}

#[test]
fn nested_source_tracer_reuses_the_actual_claim_in_ten_languages() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        let run = rt.run_litex_code(SOURCE).unwrap();
        assert!(
            run.success && run.session_error.is_none(),
            "{:?}",
            run.session_error
        );
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(last)) =
            run.statement_results.last().unwrap()
        else {
            panic!("reused forall");
        };
        let VerifyFactResult::ForallFact(result) = &last.verify_result else {
            panic!("forall result");
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
            result.as_ref()
        else {
            panic!("actual whole-source citation");
        };
        let Fact::ForallFact(source) = rt.fact_by_id_in_stack(proof.cite_fact_id).unwrap() else {
            panic!("stored source");
        };
        assert_eq!(source.dom_facts.len(), 4);
        assert_eq!(proof.parameter_renamings.len(), 7);
        let detail =
            crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &rt)
                .stringify();
        assert!(
            detail.contains("by_known_forall_fact")
                && detail.contains(&proof.cite_fact_id.to_string())
        );
        crate::json_output::project_stmt_normal(run.statement_results.last().unwrap(), &rt);
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn dependent_nested_conditions_match_without_publication_and_keep_wd_ceiling() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(rt.run_litex_code(prefix()).unwrap().success);
    let code="forall A finite_set,m N+,h fn(z A)R,p,q fn(t closed_range(1,m))A,left,right fn(t closed_range(1,m))R:\n    forall w A:\n        exist! r closed_range(1,m) st {p(r)=w}\n    forall w A:\n        exist! r closed_range(1,m) st {q(r)=w}\n    left=fn(r closed_range(1,m))R{h(p(r))}\n    right=fn(s closed_range(1,m))R{h(q(s))}\n    =>:\n        sum(1,m,left)=sum(1,m,right)\n";
    let goal = parse(&mut rt, code);
    let before = sizes(&rt);
    let (cite, renamings) = rt
        .match_known_forall_source(&goal)
        .expect("nested scoped identity");
    assert_eq!(renamings.len(), 7);
    assert_eq!(before, sizes(&rt));
    let direct = rt
        .verify_fact(
            &Fact::ForallFact(goal.clone()),
            VerifyState::new(VerifyStateLevel::Direct),
        )
        .unwrap();
    let VerifyFactResult::ForallFact(direct) = direct else {
        panic!("forall");
    };
    assert!(matches!(direct.as_ref(), VerifyForallFactResult::Failed(
        crate::execute::execute_fact_stmt::verify_forall_fact::VerifyForallFactFailed::FailToVerifyWellDefined(_)
    )));
    let result = rt
        .verify_fact(&Fact::ForallFact(goal), VerifyState::top_level())
        .unwrap();
    let VerifyFactResult::ForallFact(result) = result else {
        panic!("forall");
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
        result.as_ref()
    else {
        panic!("root citation");
    };
    assert_eq!(proof.cite_fact_id, cite);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn nested_replay_keeps_unique_tag_carrier_and_both_map_conditions() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(rt.run_litex_code(prefix()).unwrap().success);
    let original = "forall ".to_owned() + SOURCE.rsplit_once("\nforall ").unwrap().1;
    for altered in [
        original.replace("exist!", "exist"),
        original.replace("exist!", "not exist"),
        original.replace("e2(idx)=x", "e1(idx)=x"),
        original.replace("closed_range(1,n)", "closed_range(0,n)"),
        original.replace("fn(x X)R", "fn(x X)C"),
    ] {
        let goal = parse(&mut rt, &altered);
        let before = sizes(&rt);
        assert!(rt.match_known_forall_source(&goal).is_none(), "{altered}");
        assert_eq!(before, sizes(&rt));
    }
    assert!(
        !rt.run_litex_code(&original.replace("exist!", "exist"))
            .unwrap()
            .success
    );
    assert!(rt.run_litex_code(&original).unwrap().success);
    assert!(!rt.run_litex_code("0=1\n").unwrap().success);
}

#[test]
fn nested_alpha_keeps_free_object_identity() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(rt.run_litex_code("have first,second R\nforall n N+:\n    forall x R:\n        exist! y R st {y=x}\n    =>:\n        first=first\n").unwrap().success);
    let same=parse(&mut rt,"forall m N+:\n    forall a R:\n        exist! b R st {b=a}\n    =>:\n        first=first\n");
    let other=parse(&mut rt,"forall m N+:\n    forall a R:\n        exist! b R st {b=a}\n    =>:\n        second=second\n");
    let before = sizes(&rt);
    assert!(rt.match_known_forall_source(&same).is_some());
    assert!(rt.match_known_forall_source(&other).is_none());
    assert_eq!(before, sizes(&rt));
}
