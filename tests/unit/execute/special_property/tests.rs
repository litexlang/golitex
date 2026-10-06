use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::stmt::Stmt;
use crate::exec_env::SpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    EqualFactSearchedProof,
    EqualitySearchProofByObjectDefinition, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FnObjDomainFnSetEvidence, ObjWellDefinedProof, ObjWellDefinedProofByDef,
};
use crate::execute::ExecStmtResult;
use crate::json_output::project_stmt_detailed;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

#[test]
fn run_examples_callable_alias_special_property() {
    let code = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/proof_nodes/equal/by_object_definition/by_fn_application/callable_alias_special_property.lit"));
    let result = runtime().run_litex_code(code).unwrap();
    assert!(
        result.success,
        "dedicated callable-alias tracer must verify"
    );
}

#[test]
fn callable_alias_reduces_with_a_real_function_equality_path() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn f(x R) R = x + 1");
    exec_ok(&mut rt, "let g = f");
    exec_ok(&mut rt, "let h = g");
    let Stmt::Fact(goal) = parse(&mut rt, "h(4) = 5") else {
        panic!("goal")
    };
    let VerifyFactResult::Equality(result) =
        rt.verify_fact(&goal, VerifyState::top_level()).unwrap()
    else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(result) = *result else {
        panic!("alias must reduce")
    };
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(wd),
        ..
    } = result.well_defined_proof.left
    else {
        panic!("fresh application WD")
    };
    let Some(FnObjDomainFnSetEvidence::InFunctionSet {
        fact_id,
        function_equal,
        ..
    }) = wd.domain_fn_set
    else {
        panic!("signature source and transport")
    };
    assert_eq!(function_equal.path.len(), 2);
    assert!(rt.top_exec_env().facts.facts_by_id.contains_key(&fact_id));
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(proof),
        ),
    ) = result.searched_proof
    else {
        panic!("function equality must own body reduction")
    };
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::FunctionBodyExpansionProof::Anonymous(expansion) = &proof.normalization.expansions[0]
    else { panic!("named function body expansion") };
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::FunctionBodySourceProof::KnownEquality(path) = &expansion.function_body
    else { panic!("stored function equality") };
    assert_eq!(path.path.len(), 3);
    for (from, to, id) in &path.path {
        let Fact::AtomicFact(AtomicFact::EqualFact(source)) =
            &rt.top_exec_env().facts.facts_by_id[id]
        else {
            panic!("real equality source")
        };
        assert!(
            (source.left.ir() == from.ir() && source.right.ir() == to.ir())
                || (source.right.ir() == from.ir() && source.left.ir() == to.ir())
        );
    }
    let result = exec_ok(&mut rt, "g(4) = 5");
    let detailed = project_stmt_detailed(&result, &rt).stringify();
    assert!(detailed.contains("function_equal"), "{detailed}");
}

#[test]
fn function_membership_from_a_hypothesis_supplies_callability_without_a_body() {
    let mut rt = runtime();
    exec_ok(
        &mut rt,
        "forall g set:\n    g $in fn(x R) R\n    =>:\n        g(4) $in R",
    );
    assert!(exec(
        &mut rt,
        "forall g set:\n    g $in fn(x R) R\n    =>:\n        g(4) = 5"
    )
    .is_failed());
    assert!(
        rt.top_exec_env().special_properties.is_empty(),
        "local function qualifications must not escape forall"
    );
}

#[test]
fn reversed_and_non_definition_equalities_supply_function_bodies() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn f(x R) R = x + 1");
    for equality in ["f = g", "g = f"] {
        exec_ok(
            &mut rt,
            &format!("forall g set:\n    {equality}\n    =>:\n        g(4) = 5"),
        );
    }
}

#[test]
fn alias_call_checks_arity_carrier_and_value() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn f(x R) R = x + 1");
    exec_ok(&mut rt, "let g = f");
    for code in ["g(4, 5) = 5", "g({4}) = 5", "g(4) = 6"] {
        assert!(exec(&mut rt, code).is_failed(), "must reject {code}");
    }
    exec_ok(&mut rt, "g(4) = 5");
}

#[test]
fn property_rows_keep_the_source_fact_and_are_idempotent() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn f(x R) R = x + 1");
    exec_ok(&mut rt, "let g = f");
    let before = property_count(&rt);
    let sources: Vec<AtomicFact> = rt
        .top_exec_env()
        .facts
        .facts_by_id
        .values()
        .filter_map(|fact| match fact {
            Fact::AtomicFact(atomic) => Some(atomic.clone()),
            _ => None,
        })
        .collect();
    for source in sources {
        rt.store_atomic_fact(&source).unwrap();
    }
    assert_eq!(before, property_count(&rt));
    for (key, properties) in &rt.top_exec_env().special_properties {
        for property in properties {
            let source = &rt.top_exec_env().facts.facts_by_id[&property.fact_id()];
            match property {
                SpecialProperty::Membership(fact) | SpecialProperty::DefaultStructView(fact) => {
                    assert_eq!(source, &Fact::AtomicFact(AtomicFact::InFact(fact.clone())));
                    assert_eq!(key, &fact.element.ir());
                }
                SpecialProperty::Equality(fact) => {
                    assert_eq!(
                        source,
                        &Fact::AtomicFact(AtomicFact::EqualFact(fact.clone()))
                    );
                    assert!(key == &fact.left.ir() || key == &fact.right.ir());
                }
            }
        }
    }
}

#[test]
fn a_failed_claim_does_not_commit_its_successful_equality_step() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have fn f(x R) R = x + 1");
    exec_ok(&mut rt, "let g = f");
    let before = (
        rt.top_exec_env().facts.facts_by_id.len(),
        property_count(&rt),
    );
    assert!(exec(&mut rt, "claim:\n    ? g(4) = 6\n    g(4) = 5").is_failed());
    assert_eq!(
        before,
        (
            rt.top_exec_env().facts.facts_by_id.len(),
            property_count(&rt)
        )
    );
    exec_ok(&mut rt, "g(4) = 5");
}

#[test]
fn ordinary_struct_membership_does_not_select_a_default_field_view() {
    let mut rt = runtime();
    exec_ok(&mut rt, "struct Point:\n    x R\n    y R");
    exec_ok(&mut rt, "have p &Point = (1, 2)");
    exec_ok(&mut rt, "p.x = p.x");
    assert!(exec(
        &mut rt,
        "forall q set:\n    q $in &Point\n    =>:\n        q.x = q.x"
    )
    .is_failed());
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn parse(rt: &mut Runtime, code: &str) -> Stmt {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1, "{code}");
    statements.remove(0)
}

fn exec(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let statement = parse(rt, code);
    rt.exec_stmt(&statement).unwrap()
}

fn exec_ok(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let result = exec(rt, code);
    assert!(!result.is_failed(), "{code}");
    result
}

fn property_count(rt: &Runtime) -> usize {
    rt.top_exec_env()
        .special_properties
        .values()
        .map(Vec::len)
        .sum()
}
