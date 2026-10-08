use crate::execute::{ExecReleaseAndExpandStmtResult, ExecStmtResult};
use crate::execute::execute_release_tuple_def_stmt::ExecReleaseTupleDefStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language })
}
fn execute(rt: &mut Runtime, source: &str) -> ExecStmtResult {
    let blocks = Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
    let statements = rt.parse(&blocks).unwrap();
    assert_eq!(statements.len(), 1);
    rt.exec_stmt(&statements[0]).unwrap()
}
fn accept(rt: &mut Runtime, source: &str) {
    let result = execute(rt, source);
    assert!(!result.is_failed(), "{source}\n{}", crate::json_output::project_stmt_detailed(&result, rt).stringify());
}
fn facts(rt: &Runtime) -> usize {
    rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).sum()
}

#[test]
fn release_tuple_def_checks_exact_contracts_without_image_cardinality() {
    let mut rt = runtime(OutputLanguage::English);
    for source in [
        "let t=(1,2)", "release tuple def t", "t $in finite_seq(union({1},{2}),2)", "t(1)=1", "t(2)=2",
        "release tuple def (1,1)", "(1,1) $in finite_seq(union({1},{1}),2)",
        "release tuple def ()", "() $in finite_seq({},0)",
        "release tuple def tuple(7)", "tuple(7) $in finite_seq({7},1)", "tuple(7)(1)=7",
        "release tuple def (R,1)", "(R,1) $in finite_seq(union({R},{1}),2)", "(R,1)(1)=R",
        "have a,b R", "release tuple def (a,b)", "(a,b) $in finite_seq(union({a},{b}),2)",
        "have p cart(R,Z)", "release tuple def p", "p $in finite_seq(union(R,Z),2)", "p(1) $in R", "p(2) $in Z",
    ] { accept(&mut rt, source); }
    for source in ["t $in finite_seq(R,3)", "t(3)=1", "() $in finite_seq(R,1)", "tuple(7) $in finite_seq(R,2)", "(1,1) $in finite_seq(R,1)", "tuple(7)=7", "(R,1) $in finite_seq(R,2)"] {
        let before = facts(&rt);
        assert!(execute(&mut rt, source).is_failed(), "{source}");
        assert_eq!(facts(&rt), before);
    }
}

#[test]
fn release_tuple_def_preserves_source_ids_and_all_language_projections() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        accept(&mut rt, "let t=(1,2)");
        let result = execute(&mut rt, "release tuple def t");
        let detailed = crate::json_output::project_stmt_detailed(&result, &rt).stringify();
        let normal = crate::json_output::project_stmt_normal(&result, &rt).stringify();
        assert!(normal.contains("finite_seq") && normal.contains("t(2)"), "{normal}");
        let latex = crate::compile_to_latex::to_latex("release tuple def t", &mut rt).unwrap();
        assert!(latex.contains("t"), "{latex}");
        assert!(detailed.contains("fn_set_member"), "{detailed}");
        assert!(detailed.contains("complete_domain"), "{detailed}");
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::TupleDef(ExecReleaseTupleDefStmtResult::Success(proof))) = result else { panic!("{detailed}") };
        assert_eq!(proof.stored.len(), 3);
        for store in &proof.stored {
            for (id, _) in store.atomic_components() {
                let fact = &rt.top_exec_env().facts.facts_by_id[&id];
                match fact {
                    crate::ast::fact::Fact::AtomicFact(crate::ast::fact::AtomicFact::InFact(fact)) => assert!(fact.line_file.is_some()),
                    crate::ast::fact::Fact::AtomicFact(crate::ast::fact::AtomicFact::EqualFact(fact)) => assert!(fact.line_file.is_some()),
                    _ => panic!("unexpected released fact"),
                }
            }
        }
        assert!(proof.statement.line_file.line > 0);
        assert_eq!(proof.statement.readable_string(), "release tuple def t");
        accept(&mut rt, "t $in finite_seq(union({1},{2}),2)");
    }
}

#[test]
fn release_tuple_def_failures_and_local_releases_publish_nothing() {
    let mut rt = runtime(OutputLanguage::English);
    accept(&mut rt, "have fn z(i1 N+) R=0");
    accept(&mut rt, "let t=(1,2)");
    for source in ["release tuple def z", "release tuple def 1", "release tuple def cart(R,Z)", "release tuple def (1/0,2)", "z $in finite_seq(R,2)", "z $in fn(k closed_range(1,2)) R", "claim:\n    ? t $in finite_seq(union({1},{2}),2)\n    release tuple def t\n    2=3"] {
        let before = facts(&rt);
        assert!(execute(&mut rt, source).is_failed(), "{source}");
        assert_eq!(facts(&rt), before, "failed release leaked: {source}");
    }
    let before = facts(&rt);
    accept(&mut rt, "sketch:\n    release tuple def t");
    assert_eq!(facts(&rt), before);
    assert!(execute(&mut rt, "t $in finite_seq(union({1},{2}),2)").is_failed());
    accept(&mut rt, "release tuple def t");
    accept(&mut rt, "t $in finite_seq(union({1},{2}),2)");
}

#[test]
fn release_tuple_def_parser_rejects_extra_tokens_and_bodies() {
    for source in ["release tuple def unknown_tuple", "release tuple def", "release tuple def (1,2) extra", "release tuple def (1,2):\n    1=1"] {
        let mut rt = runtime(OutputLanguage::English);
        let blocks = Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
        assert!(rt.parse(&blocks).is_err(), "{source}");
    }
}



#[test]
fn release_tuple_def_readable_syntax_preserves_singleton_and_nested_values() {
    let mut rt = runtime(OutputLanguage::English);
    for source in ["release tuple def tuple(7)", "release tuple def ()", "release tuple def (1,2)", "release tuple def (tuple(7),())"] {
        let tokens = Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
        let original = rt.parse(&tokens).unwrap().remove(0);
        let readable = original.readable_string();
        let tokens = Tokenizer::new().tokenize(&readable, rt.current_file.clone()).unwrap();
        let reparsed = rt.parse(&tokens).unwrap().remove(0);
        let crate::ast::stmt::Stmt::ReleaseAndExpand(crate::ast::stmt::ReleaseAndExpandStmt::ReleaseTupleDefStmt(a)) = original else { panic!() };
        let crate::ast::stmt::Stmt::ReleaseAndExpand(crate::ast::stmt::ReleaseAndExpandStmt::ReleaseTupleDefStmt(b)) = reparsed else { panic!() };
        assert_eq!(a.obj, b.obj, "{source} -> {readable}");
    }
}
