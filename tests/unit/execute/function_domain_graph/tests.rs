//! Effective-domain evidence separates function graphs from function spaces.
use crate::execute::ExecStmtResult;
use crate::json_output::{emit_run_detailed, project_stmt_detailed};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language })
}

fn execute(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1, "{code}");
    rt.exec_stmt(&statements.remove(0)).unwrap()
}

fn facts(rt: &Runtime) -> usize {
    rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).sum()
}

#[test]
fn function_graph_empty_images_and_nonempty_spaces_follow_complete_domains() {
    for code in [
        "fn_range(fn(k {}) R {0})={}",
        "fn_range(fn(k closed_range(1,0)) R {0})={}",
        "fn_range(fn(k range(1,1)) R {0})={}",
        "have fn empty_fn(k {}) R=0\nfn_range(empty_fn)={}\nlet alias=empty_fn\nalias $in fn(k {}) R\nfn_range(alias)={}",
        "have Carrier set={}\nhave f fn(k Carrier) R\nfn_range(f)={}",
        "$is_nonempty_set(fn(k {}) {})\nhave f fn(k {}) {}\nf $in fn(k {}) R\nfn_range(f)={}",
        "$is_nonempty_set(finite_seq({},0))\nhave f finite_seq({},0)\nfn_range(f)={}",
        "have f fn(x R) fn(y R) R\nf(0)(0) $in R",
        "have f fn(x R) fn(k {}) {}\nfn_range(f(0))={}",
        "have ReturnedCarrier set=fn(k {}) {}\nhave ReturnedAlias set=ReturnedCarrier\nReturnedAlias=fn(k {}) {}\nhave f fn(x R) ReturnedAlias\nfn_range(f(0))={}",
        "have Scalar set=R\nhave f fn(x R) Scalar\nf(0) $in R",
        "have CartReturns set=cart(R,Z)\nhave f fn(x R) CartReturns\nf(0)(2) $in Z",
        "have EmptyReturns set=finite_seq({},0)\nhave f fn(x R) EmptyReturns\nfn_range(f(0))={}",
        "$is_nonempty_set(seq(fn(k {}) {}))\nhave f seq(fn(k {}) {})\nfn_range(f(1))={}",
        "$is_nonempty_set(finite_seq(fn(k {}) {},2))\nhave f finite_seq(fn(k {}) {},2)\nfn_range(f(2))={}",
        "have f fn(k R) R\n$is_nonempty_set(f)",
        "have p finite_seq(R,2)\n$is_nonempty_set(p)",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}\n{}", emit_run_detailed(&run, &rt, "function-graph-empty", None));
        assert!(run.statement_results.iter().all(|statement| !statement.is_failed()));
    }
}

#[test]
fn function_graph_inhabited_images_require_actual_inputs_and_guards() {
    for code in [
        "fn_range(fn(k R) R {0})={0}\n$is_nonempty_set(fn(k R) R {0})",
        "fn_range(fn(k closed_range(1,2)) R {0})={0}",
        "fn_range(fn(k N+: k>0) R {0})={0}\n$is_nonempty_set(fn(k N+: k>0) R {0})",
        "witness exist k R st {k>0} from 2\nfn_range(fn(k R: k>0) R {0})={0}\n$is_nonempty_set(fn(k R: k>0) R {0})",
        "fn_range(fn(x R,y {}) R {0})={}",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}\n{}", emit_run_detailed(&run, &rt, "function-graph-inputs", None));
    }
}

#[test]
fn function_graph_false_nonempty_images_and_empty_carrier_declarations_do_not_commit() {
    for (setup, target) in [
        ("1=1", "$is_nonempty_set(fn(k {}) R {0})"),
        ("1=1", "fn_range(fn(k {}) R {0})={0}"),
        ("1=1", "$is_nonempty_set(fn(k R: k>0,k<0) R {0})"),
        ("1=1", "fn_range(fn(k R: k>0,k<0) R {0})={0}"),
        ("1=1", "fn_range(fn(k R) R {0})={}"),
        ("have fn empty_fn(k {}) R=0\nlet alias=empty_fn\nalias $in fn(k {}) R", "fn_range(alias)={0}"),
        ("1=1", "have impossible fn(k R) {}"),
        ("1=1", "have impossible fn(k {}) R {0}"),
        ("1=1", "$is_nonempty_set(fn(x R,y {}) R {0})"),
        ("have f fn(x R) fn(k {}) {}", "f(0)(0) $in R"),
        ("have f fn(k {}) R", "$is_nonempty_set(f)"),
        ("have Space set=fn(k R) R", "fn_range(Space)={}"),
        ("1=1", "fn_range(cart(R,Z))={}"),
        ("have EmptyReturns set=fn(k R) {}", "have impossible fn(x R) EmptyReturns"),
        ("1=1", "forall Carrier set:\n    Carrier=fn(k R) Carrier\n    =>:\n        $is_nonempty_set(fn(x R) Carrier)"),
        ("1=1", "forall A,B set:\n    A=fn(k R) B\n    B=fn(k R) A\n    =>:\n        $is_nonempty_set(fn(x R) A)"),
        ("1=1", "have impossible fn(x R) cart(R,{})"),
        ("1=1", "$is_nonempty_set(seq(fn(k R) {}))"),
        ("1=1", "$is_nonempty_set(finite_seq(fn(k R) {},2))"),
        ("have f finite_seq(fn(k {}) {},2)", "fn_range(f(3))={}"),
        ("have CartReturns set=cart(R,Z)", "CartReturns(2) $in Z"),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(rt.run_litex_code(setup).unwrap().success, "{setup}");
        let before = facts(&rt);
        assert!(execute(&mut rt, target).is_failed(), "accepted false target: {setup}\n{target}");
        assert_eq!(facts(&rt), before, "failed target published: {target}");
        assert!(!execute(&mut rt, "1=1").is_failed());
    }
}

#[test]
fn function_graph_domain_sources_and_witnesses_survive_all_output_languages() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        assert!(rt.run_litex_code("have Carrier set={}\nhave f fn(k Carrier) R").unwrap().success);
        let result = execute(&mut rt, "fn_range(f)={}");
        assert!(!result.is_failed());
        let detailed = project_stmt_detailed(&result, &rt).stringify();
        assert!(detailed.contains("FnRangeOfEmptyDomain"), "{language:?}: {detailed}");
        assert!(detailed.contains("exact_function_membership"), "missing membership source: {detailed}");
        assert!(detailed.contains("empty_literal_carrier"), "missing carrier emptiness: {detailed}");
        let result = execute(&mut rt, "fn_range(fn(k R) R {0})={0}");
        assert!(!result.is_failed());
        let detailed = project_stmt_detailed(&result, &rt).stringify();
        assert!(detailed.contains("checked_domain_argument_witness"), "missing actual input: {detailed}");
        assert!(rt.run_litex_code("have ReturnedCarrier set=fn(k {}) {}\nhave ReturnedAlias set=ReturnedCarrier\nReturnedAlias=fn(k {}) {}").unwrap().success);
        let result = execute(&mut rt, "have outer fn(x R) ReturnedAlias");
        assert!(!result.is_failed());
        let detailed = project_stmt_detailed(&result, &rt).stringify();
        assert!(detailed.contains("checked_nonempty_return_carrier_transport"), "missing existence carrier transport: {detailed}");
        let result = execute(&mut rt, "have cart_outer fn(x R) cart(R,Z)");
        assert!(!result.is_failed());
        let detailed = project_stmt_detailed(&result, &rt).stringify();
        assert!(detailed.contains("finite_cartesian_product_exists"), "missing finite factor existence: {detailed}");
    }
}

#[test]
fn function_graph_closed_index_certificates_remain_valid_at_direct_permission() {
    use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
    for (source, expected) in [
        ("2 $in closed_range(1,2)", true),
        ("2 $in range(1,3)", true),
        ("2 $in range(1,2)", false),
        ("0 $in closed_range(1,2)", false),
        ("1.5 $in closed_range(1,2)", false),
        ("3 $in closed_range(1,2)", false),
        ("not 2 $in range(1,2)", true),
        ("not 1.5 $in closed_range(1,2)", true),
        ("2 $in closed_range(3,1)", false),
        ("not 2 $in closed_range(3,1)", true),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
        let statement = rt.parse(&tokens).unwrap().remove(0);
        let crate::ast::stmt::Stmt::Fact(fact) = statement else { panic!("{source}"); };
        let result = rt.verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct)).unwrap();
        assert_eq!(!result.is_failed(), expected, "{source}");
        assert_eq!(facts(&rt), 0, "verification published: {source}");
    }
}

const GUARD_EXCLUSION: &str = "forall k R:\n    k<0\n    =>:\n        not k>0";

#[test]
fn guarded_empty_complete_domains_share_graph_image_and_space_evidence() {
    for code in [
        "fn(k R:k>0,k<0) R {0}={}",
        "fn_range(fn(k R:k>0,k<0) R {0})={}",
        "fn(k R:k>0,k<0) {} = {()}",
        "$is_nonempty_set(fn(k R:k>0,k<0) {})",
        "have fn empty_guard(k R:k>0,k<0) R=0\nempty_guard={}\nfn_range(empty_guard)={}",
        "have f fn(k R:k>0,k<0) {}\nf={}\nfn_range(f)={}",
    ] {
        let mut rt=runtime(OutputLanguage::English);
        assert!(rt.run_litex_code(GUARD_EXCLUSION).unwrap().success);
        let run=rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}\n{}", emit_run_detailed(&run,&rt,"guard-exclusion",None));
        assert!(run.statement_results.iter().all(|stmt| !stmt.is_failed()));
    }
}

#[test]
fn guarded_domain_exclusion_preserves_permissions_scope_and_rejection_boundaries() {
    use crate::ast::obj::{FunctionSpace, Obj};
    use crate::execute::execute_fact_stmt::function_domain::FunctionDomainEmptyProof;
    use crate::execute::execute_fact_stmt::{VerifyState,VerifyStateLevel};
    let mut rt=runtime(OutputLanguage::English);
    assert!(rt.run_litex_code(GUARD_EXCLUSION).unwrap().success);
    let tokens=Tokenizer::new().tokenize("fn(k R:k>0,k<0) {} = {()}",rt.current_file.clone()).unwrap();
    let statement=rt.parse(&tokens).unwrap().remove(0);
    let crate::ast::stmt::Stmt::Fact(crate::ast::fact::Fact::AtomicFact(crate::ast::fact::AtomicFact::EqualFact(fact)))=statement else { panic!("function space equality"); };
    let Obj::FunctionSpace(FunctionSpace::FnSet(signature))=fact.left else { panic!("function signature"); };
    let before=facts(&rt);
    let depth=rt.execution_environments_stack.len();
    for level in [VerifyStateLevel::Direct,VerifyStateLevel::KnownSpecialProperty,VerifyStateLevel::BuiltinRule] {
        let proof=rt.verify_function_domain_empty(&signature,VerifyState::new(level)).unwrap().unwrap();
        assert!(matches!(proof,FunctionDomainEmptyProof::GuardExclusion(_)));
        assert_eq!(facts(&rt),before,"scoped exclusion published an assumption");
        assert_eq!(rt.execution_environments_stack.len(),depth);
    }
    for target in [
        "fn(k R:k>0) R {0}={}",
        "fn_range(fn(k R:k<0) R {0})={}",
        "fn(k R:k>0) {} = {()}",
        "fn(k R:k>0,k>1) R {0}={}",
        "fn(k R:k>0,k<0) R {0}={0}",
        "2=3",
    ] {
        let before=facts(&rt);
        assert!(execute(&mut rt,target).is_failed(),"false domain exclusion accepted: {target}");
        assert_eq!(facts(&rt),before,"failed domain target published: {target}");
    }
    assert!(!execute(&mut rt,"1=1").is_failed());
}

#[test]
fn guarded_domain_exclusion_retains_checked_forall_sources_in_ten_languages() {
    for language in OutputLanguage::ALL {
        let mut rt=runtime(language);
        assert!(rt.run_litex_code(GUARD_EXCLUSION).unwrap().success);
        for target in ["fn(k R:k>0,k<0) R {0}={}","fn_range(fn(k R:k>0,k<0) R {0})={}","fn(k R:k>0,k<0) {} = {()}","have fn empty_bound(k R:k>0,k<0) {}=0"] {
            let result=execute(&mut rt,target);
            assert!(!result.is_failed(),"{language:?}: {target}");
            let detailed=project_stmt_detailed(&result,&rt).stringify();
            assert!(detailed.contains("checked_guard_input_exclusion"),"missing guard proof: {detailed}");
            assert!(detailed.contains("ByKnownForallFact") || detailed.contains("by_known_forall"),"missing actual theorem source: {detailed}");
            if target.starts_with("have fn") {
                assert!(detailed.contains("return_bound_vacuous_empty_domain"),"missing vacuous return evidence: {detailed}");
                assert!(detailed.contains("body_well_defined"),"missing mandatory body WD: {detailed}");
            }
            crate::knowledge_base::JsonValue::parse(&detailed).unwrap();
        }
    }
}

#[test]
fn anonymous_empty_complete_domains_check_body_wd_and_vacuous_return_bounds() {
    for code in [
        "have fn empty_value(k {}) {}=0\nempty_value={}\nfn_range(empty_value)={}",
        "have fn empty_value(k closed_range(1,0)) {}=0\nempty_value={}",
        "have fn empty_value(k R:k>0,k<0) {}=0\nempty_value={}\nfn_range(empty_value)={}",
        "have fn empty_value(k R:k>0,k<0) {}=k\nempty_value={}",
    ] {
        let mut rt=runtime(OutputLanguage::English);
        assert!(rt.run_litex_code(GUARD_EXCLUSION).unwrap().success);
        let run=rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none(),"{code}\n{}",emit_run_detailed(&run,&rt,"empty-constructor",None));
        let detailed=project_stmt_detailed(&run.statement_results[0],&rt).stringify();
        assert!(detailed.contains("return_bound_vacuous_empty_domain"),"missing independent void return evidence: {detailed}");
        let before=facts(&rt);
        for negative in ["0 $in {}","empty_value(1)=0","2=3"] {
            assert!(execute(&mut rt,negative).is_failed(),"vacuity published false value: {negative}");
            assert_eq!(facts(&rt),before);
        }
    }
    for target in [
        "have fn bad(k R) {}=0",
        "have fn bad(k R:k>0) {}=0",
        "have fn bad(k {}) R=1/0",
        "have fn bad(k R:k>0,k<0) R=1/0",
    ] {
        let mut rt=runtime(OutputLanguage::English);
        assert!(rt.run_litex_code(GUARD_EXCLUSION).unwrap().success);
        let before=facts(&rt);
        assert!(execute(&mut rt,target).is_failed(),"bad body or nonempty return domain accepted: {target}");
        assert_eq!(facts(&rt),before,"failed constructor published: {target}");
    }
    // Undefined names are rejected by the parser before a body-WD result
    // exists. Check that boundary through the actual source pipeline.
    let mut rt=runtime(OutputLanguage::English);
    let before=facts(&rt);
    let run=rt.run_litex_code("have fn bad(k {}) R=missing_value").unwrap();
    assert!(!run.success && run.session_error.is_some());
    assert_eq!(facts(&rt),before);
}

#[test]
fn internal_zero_parameter_signature_has_one_input_assignment() {
    use crate::ast::obj::{AnonymousFn,FnSet,FunctionSpace,Literal,Number,Obj,SetFormer,ListSet,StandardSet};
    use crate::ast::param::SetBoundParameterList;
    use crate::execute::execute_fact_stmt::{VerifyState,VerifyObjWellDefinedResult};
    // The surface parser currently requires a parameter; this is the shared
    // signature invariant for an empty parameter list, distinct from I_0.
    for (return_set,expected) in [
        (Obj::StandardSet(StandardSet::R),true),
        (Obj::SetFormer(SetFormer::ListSet(ListSet{list:vec![]})),false),
    ] {
        let mut rt=runtime(OutputLanguage::English);
        let value=Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
            body:FnSet {set_bound_parameters:SetBoundParameterList{groups:vec![]},dom_facts:vec![],ret_set:Box::new(return_set)},
            equal_to:Box::new(Obj::Literal(Literal::Number(Number{normalized_value:"0".into()}))),
        }));
        let before=facts(&rt);
        let result=rt.verify_obj_well_definedness(&value,VerifyState::top_level()).unwrap();
        assert_eq!(matches!(result,VerifyObjWellDefinedResult::Success(_)),expected);
        assert_eq!(facts(&rt),before,"WD must not publish a return fact");
    }
}
