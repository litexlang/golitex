use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::obj::{Obj, ProductShape};
use crate::ast::stmt::Stmt;
use crate::json_output::{emit_run_detailed, project_stmt_normal};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true,
        language: OutputLanguage::English,
    })
}

fn object(rt: &mut Runtime, source: &str) -> Obj {
    let blocks = Tokenizer::new().tokenize(&format!("{source} = {source}"), rt.current_file.clone()).unwrap();
    let statements = rt.parse(&blocks).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(fact))) = &statements[0] else { panic!("equality"); };
    fact.left.clone()
}

fn accepted(rt: &mut Runtime, source: &str) {
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none(), "{source}\n{}", emit_run_detailed(&run, rt, "exact-properties", None));
    assert!(run.statement_results.iter().all(|stmt| !stmt.is_failed()));
}

fn facts(rt: &Runtime) -> usize {
    rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).sum()
}

#[test]
fn exact_property_lookup_does_not_discover_transitive_bodies_signatures_or_coordinates() {
    let mut rt = runtime();
    accepted(&mut rt, "have fn step(x R) R = x+1\nlet first=step\nlet second=first\nlet pair=(1,2)\nlet pair_alias=pair\nhave Carrier set=finite_seq(R,2)\nhave CarrierAlias set=Carrier");
    let step = object(&mut rt, "step");
    let second = object(&mut rt, "second");
    let pair = object(&mut rt, "pair");
    let pair_alias = object(&mut rt, "pair_alias");
    let carrier_alias = object(&mut rt, "CarrierAlias");
    assert!(!rt.collect_in_function_set_candidates(&step).is_empty());
    assert!(rt.collect_in_function_set_candidates(&second).is_empty());
    assert!(rt.complete_function_domains(&second, crate::execute::execute_fact_stmt::VerifyState::top_level()).unwrap().is_empty());
    assert_eq!(rt.known_literal_tuple_candidates(&pair).len(), 1);
    assert!(rt.known_literal_tuple_candidates(&pair_alias).is_empty());
    assert!(rt.returned_function_signature(&carrier_alias).is_none());
    assert!(rt.exact_property_equality_path(&second, &step).is_none());
    let before = facts(&rt);
    let run = rt.run_litex_code("second(3)=4").unwrap();
    assert!(!run.success && run.session_error.is_none());
    let normal = project_stmt_normal(&run.statement_results[0], &rt).stringify();
    assert!(normal.contains("well_defined"), "{normal}");
    assert_eq!(facts(&rt), before, "failed call published facts");
    accepted(&mut rt, "second=step\nsecond=fn(x R) R {x+1}\nsecond(3)=4");
    let candidates = rt.exact_property_object_values(&second);
    assert!(candidates.iter().all(|(_, path)| path.len() <= 1));
    let (_, path) = candidates.iter().find(|(value, _)| matches!(value,
        Obj::FunctionSpace(crate::ast::obj::FunctionSpace::AnonymousFn(_)))).unwrap();
    assert_eq!(path.len(), 1);
    assert!(rt.fact_by_id_in_stack(path[0].2).is_some());
    accepted(&mut rt, "pair_alias=(1,2)\npair_alias(2)=2\nCarrierAlias=finite_seq(R,2)");
    assert_eq!(rt.known_literal_tuple_candidates(&pair_alias).len(), 1);
    assert!(rt.returned_function_signature(&carrier_alias).is_some());
}

#[test]
fn exact_property_lookup_reads_both_equality_orientations_and_preserves_normal_equality() {
    for equality in ["alias=fn(t R) R {t+1}", "fn(t R) R {t+1}=alias"] {
        let mut rt = runtime();
        accepted(&mut rt, "have fn step(x R) R=x+1\nlet alias=step");
        let alias = object(&mut rt, "alias");
        assert!(rt.collect_in_function_set_candidates(&alias).is_empty());
        accepted(&mut rt, equality);
        accepted(&mut rt, "alias(3)=4");
        let before = facts(&rt);
        assert!(!rt.run_litex_code("alias(3)=5").unwrap().success);
        assert!(!rt.run_litex_code("alias({})=4").unwrap().success);
        assert_eq!(facts(&rt), before);
    }
    let mut rt = runtime();
    accepted(&mut rt, "have a R\nlet b=a\nlet c=b\na=c");
    let a = object(&mut rt, "a");
    let c = object(&mut rt, "c");
    // Normal equality remains allowed to publish this exact endpoint.
    assert_eq!(rt.exact_property_equality_path(&a, &c).unwrap().len(), 1);
}

#[test]
fn exact_property_lookup_stable_tracer_and_template_guards() {
    let source = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/equal/by_object_definition/by_fn_application/exact_property_function_lookup.lit"));
    accepted(&mut runtime(), source);
    let mut rt = runtime();
    accepted(&mut rt, "template<a R+>:\n    have fn shift(x R) R=x+a\nlet valid=\\shift<2>\nvalid(3)=5");
    let before = facts(&rt);
    assert!(!rt.run_litex_code("let invalid=\\shift<0>").unwrap().success);
    assert_eq!(facts(&rt), before);
    accepted(&mut rt, "have signature_only fn(x R) R\nsignature_only(3) $in R");
    assert!(!rt.run_litex_code("signature_only(3)=4").unwrap().success);
    let pair = object(&mut rt, "(1,2)");
    assert!(matches!(pair, Obj::ProductShape(ProductShape::Tuple(_))));
}
