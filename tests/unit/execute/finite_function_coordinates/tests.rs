use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::obj::{Obj, ProductShape};
use crate::execute::ExecStmtResult;
use crate::json_output::{project_stmt_detailed, project_stmt_normal};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language,
    })
}

fn execute(rt: &mut Runtime, source: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1, "{source}");
    rt.exec_stmt(&statements.remove(0)).unwrap()
}

fn fact_count(rt: &Runtime) -> usize {
    rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).sum()
}

fn retired_object(obj: &Obj) -> bool {
    matches!(obj, Obj::ProductShape(ProductShape::ObjAtIndex(_)
        | ProductShape::TupleDim(_) | ProductShape::CartDim(_) | ProductShape::Proj(_)))
}

fn assert_no_retired_product_facts(rt: &Runtime) {
    for env in &rt.execution_environments_stack {
        for fact in env.facts.facts_by_id.values() {
            let retired = match fact {
                Fact::AtomicFact(AtomicFact::IsTupleFact(_) | AtomicFact::NotIsTupleFact(_)
                    | AtomicFact::IsCartFact(_) | AtomicFact::NotIsCartFact(_)) => true,
                Fact::AtomicFact(AtomicFact::EqualFact(eq)) => retired_object(&eq.left) || retired_object(&eq.right),
                Fact::AtomicFact(AtomicFact::InFact(member)) => retired_object(&member.element) || retired_object(&member.set),
                _ => false,
            };
            assert!(!retired, "retired product fact published: {}", fact.readable_string());
        }
    }
}

#[test]
fn finite_function_coordinates_stored_members_and_literal_aliases_need_no_shape_facts() {
    for source in [
        "have p cart(R,Z)\np(1) $in R\np(2) $in Z\nlet alias=p\nalias(2) $in Z",
        "let p=(1,2)\np(1)=1\np(2)=2\np $in finite_seq(Z,2)",
        "let p=tuple(7)\np(1)=7\np $in cart(Z)",
        "let p=()\np $in cart()\np={}",
        "have Carrier set=cart(R,Z)\nhave p Carrier=(1,2)\nhave alias Carrier=p\nalias(2) $in Z",
        "have fn f(k closed_range(1,2)) Z=0\nf $in cart(R,Z)\nf(2) $in Z",
        "have fn maker(x R) cart(R,Z)=(x,2)\nmaker(3)(2) $in Z",
        "have fn next(x R) R=x+1\nhave operations cart(fn(x R) R,Z)=(next,7)\noperations(1)(2)=3",
        "struct Guarded:\n    point R\n    call fn(x R:x=point) R\nhave fn at_zero(x R:x=0) R=0\nhave guarded &Guarded=(0,at_zero)\nguarded.point=guarded(1)=0\nguarded(2)(guarded.point)=0",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{source}\n{}", crate::json_output::emit_run_detailed(&run, &rt, "finite-coordinates", None));
        assert!(run.statement_results.iter().all(|statement| !statement.is_failed()));
        assert_no_retired_product_facts(&rt);
    }
}

#[test]
fn finite_function_coordinates_struct_bridges_preserve_order_fields_and_dependent_types() {
    for file in [
        "examples/infer/atomic/cart_exact_function_coordinates.lit",
        "examples/stmt_nodes/definition/struct_function_coordinate_bridges.lit",
        "examples/infer/atomic/in_cart_projection.lit",
        "examples/proof_nodes/equal/by_object_definition/by_fn_application/finite_function_coordinate_call.lit",
    ] {
        let source = std::fs::read_to_string(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(file)).unwrap();
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(&source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{file}\n{}", crate::json_output::emit_run_detailed(&run, &rt, "finite-coordinates", None));
        assert!(!run.statement_results.is_empty());
        assert!(run.statement_results.iter().all(|statement| !statement.is_failed()));
        assert_no_retired_product_facts(&rt);
    }
}

#[test]
fn finite_function_coordinates_nested_beta_retains_actual_sources_and_inner_domain_checks() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        let run = rt.run_litex_code("have fn next(x R) R=x+1\nhave operations cart(fn(x R) R,Z)=(next,7)\noperations(1)(2)=3").unwrap();
        assert!(run.success && run.session_error.is_none(), "{language:?}");
        let detailed = project_stmt_detailed(run.statement_results.last().unwrap(), &rt).stringify();
        assert!(detailed.contains("finite_function_coordinate"), "{detailed}");
        assert!(detailed.contains("application_well_defined") && detailed.contains("body_application_well_defined"), "missing real coordinate or selected-body WD: {detailed}");
        assert!(detailed.contains("continued_body") && detailed.contains("next(2)"), "missing continued ordinary call: {detailed}");
        assert!(detailed.contains("function_equal"), "missing actual function equality source: {detailed}");
        let before = fact_count(&rt);
        assert!(execute(&mut rt, "operations(1)(2)=4").is_failed());
        assert_eq!(fact_count(&rt), before);
        assert_no_retired_product_facts(&rt);
    }
}

#[test]
fn finite_function_coordinates_reject_wrong_fields_domains_and_guards_without_publishing() {
    for (setup, goal) in [
        ("have p cart(R,Z)", "p(1) $in Z"),
        ("have p cart(R,Z)", "p(3) $in Z"),
        ("struct Pair:\n    first R\n    second Z\nhave p &Pair=(1/2,2)", "p(1) $in Z"),
        ("struct Pair:\n    first R\n    second Z\nhave p &Pair=(1/2,2)", "p.first=p(2)"),
        ("struct Pair:\n    first R\n    second Z\nhave p &Pair=(1/2,2)", "p(3)=p.second"),
        ("struct CarrierValue:\n    carrier power_set(R)\n    value carrier", "have item &CarrierValue=({0},1)"),
        ("struct Guarded:\n    point R\n    call fn(x R:x!=0) R", "forall s &Guarded:\n    s.call(0)=s.call(0)"),
        ("struct Guarded:\n    point R\n    call fn(x R:x=point) R\nhave fn at_zero(x R:x=0) R=0\nhave guarded &Guarded=(0,at_zero)", "guarded(3)(0)=0"),
        ("struct Guarded:\n    point R\n    call fn(x R:x=point) R\nhave fn at_zero(x R:x=0) R=0\nhave guarded &Guarded=(0,at_zero)", "guarded(1)(0)=0"),
        ("struct Guarded:\n    point R\n    call fn(x R:x=point) R\nhave fn at_zero(x R:x=0) R=0\nhave guarded &Guarded=(0,at_zero)", "guarded(2)(1)=0"),
        ("struct Guarded:\n    point R\n    call fn(x R:x=point) R\nhave fn at_zero(x R:x=0) R=0\nhave guarded &Guarded=(0,at_zero)", "guarded(2)(())=0"),
        ("struct Guarded:\n    point R\n    call fn(x R:x=point) R\nhave fn at_zero(x R:x=0) R=0\nhave guarded &Guarded=(0,at_zero)", "guarded(2)(guarded.point)=1"),
        ("cart({},R)={}\ncart({},R,Z)={}", "2=3"),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(rt.run_litex_code(setup).unwrap().success, "{setup}");
        let before = fact_count(&rt);
        let result = execute(&mut rt, goal);
        assert!(result.is_failed(), "false goal accepted: {setup}\n{goal}");
        assert_eq!(fact_count(&rt), before, "failed coordinate target published: {goal}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert_no_retired_product_facts(&rt);
    }
    let mut rt = runtime(OutputLanguage::English);
    let before = fact_count(&rt);
    assert!(rt.run_litex_code("sketch:\n    struct Local:\n        first R\n        second Z\n    have point &Local=(1,2)\n    point.second=point(2)").unwrap().success);
    assert_eq!(fact_count(&rt), before);
    assert!(rt.def_struct_visible_in_stack("Local").is_none());
}

#[test]
fn finite_function_coordinates_local_struct_bridge_output_uses_ordinary_applications() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        assert!(rt.run_litex_code("struct Pair:\n    first R\n    second Z").unwrap().success);
        let result = execute(&mut rt, "forall p &Pair:\n    p.first=p(1)\n    p.second=p(2)\n    p(2) $in Z");
        assert!(!result.is_failed(), "{language:?}");
        let detailed = project_stmt_detailed(&result, &rt).stringify();
        assert!(detailed.contains("auto_opened_struct_layers"), "{language:?}: {detailed}");
        assert!(detailed.contains("p.first = p(1)") && detailed.contains("p.second = p(2)"), "missing actual field bridges: {detailed}");
        for retired in ["tuple_dim", "cart_dim", "$is_tuple", "p[1]", "p[2]"] {
            assert!(!detailed.contains(retired), "retired bridge in Detailed: {retired}");
        }
        assert!(project_stmt_normal(&result, &rt).stringify().contains("p(2)"));
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert_no_retired_product_facts(&rt);
    }
}
