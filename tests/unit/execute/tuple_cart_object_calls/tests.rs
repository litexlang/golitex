use crate::ast::fact::Fact;
use crate::execute::ExecStmtResult;
use crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language })
}
fn execute(rt: &mut Runtime, source: &str) -> ExecStmtResult {
    let blocks=Tokenizer::new().tokenize(source,rt.current_file.clone()).unwrap();
    let statements=rt.parse(&blocks).unwrap();
    assert_eq!(statements.len(),1);
    rt.exec_stmt(&statements[0]).unwrap()
}
fn facts(rt: &Runtime) -> usize { rt.execution_environments_stack.iter().map(|env|env.facts.facts_by_id.len()).sum() }

#[test]
fn object_head_calls_and_eval_preserve_layers_types_and_rollback() {
    let mut rt=runtime(OutputLanguage::English);
    for source in ["(1,2)(1)=1", "((1,2),3)(1)(2)=2", "tuple(7)(1)=7", "(1,2)(2) $in Z", "eval (1,2)(2)", "have fn f(x R) fn(y R) R=fn(y R) R {x+y}", "f(2)=fn(y R) R {2+y}", "(f(2))(3)=5"] {
        assert!(!execute(&mut rt,source).is_failed(),"{source}");
    }
    for source in ["(1,2)(3)=3", "((1,2),3)(2)(1)=1", "(1)(1)=1", "()(1)=1", "tuple(7)(2)=7", "(1,2)(1,2)=1", "cart(R,Z)(1)=1", "(1/2,2)(1) $in Z", "(1,2)(1)=2"] {
        let before=facts(&rt);
        assert!(execute(&mut rt,source).is_failed(),"{source}");
        assert_eq!(facts(&rt),before,"failed object call published: {source}");
    }
}

#[test]
fn release_cart_def_publishes_complete_equation_with_source_and_reusable_fact_id() {
    for language in OutputLanguage::ALL {
        let mut rt=runtime(language);
        for source in ["release cart def cart(R,Z)","release cart def cart(R)","release cart def cart()"] {
            let result=execute(&mut rt,source);
            let detailed=crate::json_output::project_stmt_detailed(&result,&rt).stringify();
            let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::CartDef(ExecReleaseCartDefStmtResult::Success(proof)))=result else {panic!("{source}: {detailed}")};
            assert!(proof.verification.fact.line_file.is_some());
            assert!(rt.top_exec_env().facts.facts_by_id.contains_key(&proof.verification.fact.fact_id));
            assert!(detailed.contains("finite_seq"),"{detailed}");
        }
        for source in ["cart(R,Z)={p finite_seq(union(R,Z),2):p(1) $in R,p(2) $in Z}","cart(R)={p finite_seq(R,1):p(1) $in R}","cart()=finite_seq({},0)","have p cart(R,Z)=(1,2)","p(2) $in Z"] {
            assert!(!execute(&mut rt,source).is_failed(),"{source}");
        }
        let before=facts(&rt);
        assert!(execute(&mut rt,"release cart def cart(R,1/0)").is_failed());
        assert_eq!(facts(&rt),before);
        assert!(!execute(&mut rt,"sketch:\n    release cart def cart(R,Z,N)").is_failed());
        assert_eq!(facts(&rt),before,"sketch release leaked");
        for fact in rt.top_exec_env().facts.facts_by_id.values() {
            if let Fact::AtomicFact(crate::ast::fact::AtomicFact::EqualFact(eq))=fact {
                assert!(!Fact::from(eq.clone()).readable_string().contains("cart_dim"));
            }
        }
    }
}

#[test]
fn function_valued_coordinates_use_the_checked_returned_body_and_guards() {
    let mut rt = runtime(OutputLanguage::English);
    for source in include_str!("../../../../examples/proof_nodes/equal/by_object_definition/by_fn_application/function_valued_tuple_call.lit")
        .lines().map(str::trim).filter(|line| !line.is_empty() && !line.starts_with('#')) {
        let result = execute(&mut rt,source);
        assert!(!result.is_failed(),"{source}");
        if source.starts_with("eval") {
            let detailed = crate::json_output::project_stmt_detailed(&result,&rt).stringify();
            assert!(detailed.contains("returned_anonymous_function_application"),"{detailed}");
            assert!(detailed.contains("application_well_defined"),"{detailed}");
        }
    }
    for source in [
        "functions(1)(0)=0",
        "functions(1)(1,2)=1",
        "(fn(x R) R {x},0)(1)(i)=i",
        "(fn(x R) R {x},0)(2)(1)=1",
        "(fn(x R) R {x},0)(1)(2)=3",
    ] {
        let before = facts(&rt);
        assert!(execute(&mut rt,source).is_failed(),"{source}");
        assert_eq!(facts(&rt),before,"failed returned function published: {source}");
    }
}
