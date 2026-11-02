use litex::ast::stmt::Stmt;
use litex::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::result_detail::OutputDetail;
use litex::runtime::Runtime;
use litex::tokenize::Tokenizer;

const HEADER: &str = "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K";
const RING: &str = "$comm_ring(K,add,mul,neg,zero,one)";
const SQUARE: &str = "mul(add(a,b),add(a,neg(b)))=add(mul(a,a),neg(mul(b,b)))";
const REAL_SETUP: &str = "have fn shifted_add(x,y R) R = x+y+1\nhave fn shifted_mul(x,y R) R = x*y+x+y\nhave fn shifted_neg(x R) R = -x-2\nby def $comm_ring(R,shifted_add,shifted_mul,shifted_neg,-1,0)\n";

fn runtime(detail: OutputDetail, language: OutputLanguage) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        },
        detail,
    )
}
fn detailed() -> Runtime {
    runtime(OutputDetail::Detailed, OutputLanguage::English)
}
fn accepts(rt: &mut Runtime, source: &str) -> String {
    let result = rt.run_litex_code(source).unwrap();
    let output = if rt.result_detail() == OutputDetail::Detailed {
        litex::json_output::emit_run_detailed(&result, rt, "test", None)
    } else {
        String::new()
    };
    assert!(
        result.success && result.session_error.is_none(),
        "{source}: {output}"
    );
    output
}
fn rejects(rt: &mut Runtime, source: &str) {
    let result = rt.run_litex_code(source).unwrap();
    assert!(
        !result.success && result.session_error.is_none(),
        "accepted {source}"
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}
fn goal(expression: &str, extra: &str, premises: &[&str]) -> String {
    format!(
        "{HEADER}{extra}:\n{}    =>:\n        {expression}\n",
        premises
            .iter()
            .map(|p| format!("    {p}\n"))
            .collect::<String>()
    )
}

#[test]
fn abstract_rings_normalize_and_compose_original_constructor_congruence() {
    for (expression, extra, premises) in [
        (SQUARE, "", vec![RING]),
        ("add(add(a,b),c)=add(b,add(c,a))", "", vec![RING]),
        ("add(mul(a,b),mul(a,c))=mul(a,add(b,c))", "", vec![RING]),
        ("mul(neg(a),neg(b))=mul(a,b)", "", vec![RING]),
        ("mul(a,zero)=zero", "", vec![RING]),
        (
            "h(mul(add(a,b),add(a,neg(b))))=h(add(mul(a,a),neg(mul(b,b))))",
            ", h fn(x K) R",
            vec![RING],
        ),
        (
            "add(f(add(a,b)),c)=add(c,f(add(b,a)))",
            ", f fn(x K) K",
            vec![RING],
        ),
        (
            "plus(plus(a,b),c)=add(c,add(b,a))",
            ", plus fn(x,y K) K",
            vec![RING, "plus=add"],
        ),
        (
            "factory(0)(a,add(b,c))=add(c,add(b,a))",
            ", factory fn(t R) fn(x,y K) K",
            vec![RING, "factory(0)=add"],
        ),
    ] {
        let output = accepts(&mut detailed(), &goal(expression, extra, &premises));
        // The direct distributivity law keeps its earlier forall/symmetry route.
        if expression != "add(mul(a,b),mul(a,c))=mul(a,add(b,c))" {
            assert!(
                output.contains("\"rule\":\"Ring\"") || output.contains("\"rule\": \"Ring\""),
                "{expression}: {output}"
            );
            assert!(output.contains("integer_polynomial_normalization"));
            assert!(output.contains("membership") && output.contains("source"));
        }
    }
}

#[test]
fn wrong_laws_owners_domains_and_field_cancellation_are_rejected() {
    for (expression, extra, premises) in [
        ("add(a,b)=mul(a,b)", "", vec![RING]),
        (SQUARE, "", vec![]),
        (SQUARE, "", vec!["not $comm_ring(K,add,mul,neg,zero,one)"]),
        ("other(a,b)=other(b,a)", ", other fn(x,y K) K", vec![RING]),
        ("a=b", "", vec![RING, "add(a,a)=add(b,b)"]),
        ("a=one", "", vec![RING, "mul(a,a)=a"]),
        (
            "h(add(a,b))=h(add(b,a))",
            ", h fn(x K: x!=zero) K",
            vec![RING],
        ),
        ("other(a)=a", ", other fn(x R) R", vec![RING]),
    ] {
        rejects(&mut detailed(), &goal(expression, extra, &premises));
    }
}

#[test]
fn checked_definitions_support_shifted_constants_and_the_zero_ring() {
    let mut rt = detailed();
    accepts(&mut rt, REAL_SETUP);
    accepts(&mut rt,"forall a,b R:\n    shifted_mul(shifted_add(a,b),shifted_add(a,shifted_neg(b)))=shifted_add(shifted_mul(a,a),shifted_neg(shifted_mul(b,b)))\n");
    // Native 2 is an ordinary element in this ring, not its coefficient two.
    rejects(
        &mut rt,
        "forall a R:\n    shifted_add(a,a)=shifted_mul(2,a)\n",
    );
    accepts(&mut rt, "shifted_add(0,0)=1\nshifted_mul(2,0)=2\n1!=2\n");
    accepts(&mut rt,"have fn trivial_add(x,y {0}) {0} = 0\nhave fn trivial_mul(x,y {0}) {0} = 0\nhave fn trivial_neg(x {0}) {0} = 0\nby def $comm_ring({0},trivial_add,trivial_mul,trivial_neg,0,0)\n");
}

#[test]
fn bad_definition_does_not_publish_a_ring_or_its_false_laws() {
    let mut rt = detailed();
    accepts(&mut rt,"have fn real_add(x,y R) R = x+y\nhave fn real_neg(x R) R = -x\nhave fn bad_mul(x,y R) R = 0\n");
    rejects(
        &mut rt,
        "by def $comm_ring(R,real_add,bad_mul,real_neg,0,1)\n",
    );
    rejects(&mut rt, "forall a R:\n    bad_mul(1,a)=a\n");
    rejects(&mut rt,"forall add fn(x,y R: x!=0) R, mul fn(x,y R) R, neg fn(x R) R:\n    $comm_ring(R,add,mul,neg,0,1)\n    =>:\n        0=0\n");
    accepts(&mut rt, "0=0\n");
}

#[test]
fn std_ring_fields_have_a_direct_checked_native_bridge() {
    let mut rt = detailed();
    let definitions = include_str!("../std/algebra/ring.lit")
        .split("thm add_right_zero:")
        .next()
        .unwrap();
    accepts(&mut rt, definitions);
    accepts(&mut rt,"claim:\n    ? forall K nonempty_set,S &Ring<K>:\n        $is_commutative_ring(K,S)\n        =>:\n            $comm_ring(K,S.add,S.mul,S.neg,S.zero,S.one)\n    by def $comm_ring(K,S.add,S.mul,S.neg,S.zero,S.one)\n");
    accepts(&mut rt,"claim:\n    ? forall K nonempty_set,S &Ring<K>,a,b K:\n        $is_commutative_ring(K,S)\n        =>:\n            S.mul(S.add(a,b),S.add(a,S.neg(b)))=S.add(S.mul(a,a),S.neg(S.mul(b,b)))\n    by def $comm_ring(K,S.add,S.mul,S.neg,S.zero,S.one)\n    S.mul(S.add(a,b),S.add(a,S.neg(b)))=S.add(S.mul(a,a),S.neg(S.mul(b,b)))\n");
}

#[test]
fn branch_requires_the_inherited_final_rewrite_permission() {
    let mut rt = detailed();
    // Abstract operations have no function bodies that an earlier, valid
    // definition/beta route could use independently of ring normalization.
    let source = goal(SQUARE, "", &[RING]);
    let blocks = Tokenizer::new()
        .tokenize(&source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&blocks).unwrap().remove(0) else {
        panic!("fact");
    };
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
        VerifyStateLevel::BuiltinRule,
        VerifyStateLevel::Strategy,
        VerifyStateLevel::DefinitionAndForall,
    ] {
        assert!(rt
            .verify_fact(&fact, VerifyState::new(level))
            .unwrap()
            .is_failed());
    }
    assert!(rt
        .verify_fact(&fact, VerifyState::top_level().without_rewrite())
        .unwrap()
        .is_failed());
    assert!(!rt
        .verify_fact(&fact, VerifyState::top_level())
        .unwrap()
        .is_failed());
}

#[test]
fn native_predicate_arity_reservation_and_lexical_scope_are_preserved() {
    let mut rt = detailed();
    accepts(&mut rt, REAL_SETUP);
    rejects(
        &mut rt,
        "$comm_ring(R,shifted_add,shifted_mul,shifted_neg,-1)\n",
    );
    rejects(&mut rt, "prop comm_ring(x R):\n    x=x\n");
    rejects(&mut rt, "abstract_prop comm_ring(x)\n");
    // A successful conditional proof must not export its local ring assumption.
    accepts(&mut rt,"have K nonempty_set\nhave add,mul fn(x,y K) K\nhave neg fn(x K) K\nhave zero,one,a,b,c K\n");
    accepts(
        &mut rt,
        &format!("forall t K:\n    {RING}\n    =>:\n        {SQUARE}\n"),
    );
    rejects(&mut rt, SQUARE);
    rejects(
        &mut rt,
        &format!("forall t K:\n    {RING}\n    =>:\n        a=b\n"),
    );
    rejects(&mut rt, SQUARE);
}

#[test]
fn every_output_detail_and_language_keeps_the_same_verdict() {
    for detail in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        for language in OutputLanguage::ALL {
            let mut rt = runtime(detail, language);
            accepts(&mut rt, &goal(SQUARE, "", &[RING]));
            rejects(&mut rt, &goal("add(a,b)=mul(a,b)", "", &[RING]));
        }
    }
}

#[test]
fn lean_export_rejects_the_unimplemented_ring_semantics_without_an_artifact() {
    let mut rt = detailed();
    let run = rt.run_litex_code(&goal(SQUARE, "", &[RING])).unwrap();
    assert!(run.success);
    let error = litex::compile_to_lean::compile_run(&run, rt, "CommRingBoundary").unwrap_err();
    assert!(format!("{error:?}").contains("CommRing"), "{error:?}");
}

#[test]
fn durable_tracer_is_checked_without_trust() {
    accepts(
        &mut detailed(),
        include_str!("../examples/proof_nodes/equal/by_builtin_rewrite/comm_ring_polynomial.lit"),
    );
}
