use super::*;
use crate::result_detail::OutputDetail;

const TRACER: &str = include_str!(
    "../../../../examples/proof_nodes/atomic/checked_function_membership_composition.lit"
);

fn with_detail(detail: OutputDetail) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        detail,
    )
}

#[test]
fn checked_function_membership_composes_in_all_output_modes_and_consumers() {
    for detail in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        let mut rt = with_detail(detail);
        let result = rt.run_litex_code(TRACER).unwrap();
        assert!(result.success, "{detail:?}: {:?}", result.session_error);
        assert_eq!(rt.execution_environments_stack.len(), 1);
        if detail == OutputDetail::Detailed {
            let json = crate::json_output::project_stmt_detailed(&result.statement_results[0], &rt)
                .stringify();
            assert!(json.contains("by_checked_argument_membership"), "{json}");
            assert!(json.contains("function_return"), "{json}");
            assert!(json.contains("FnApplicationInCodomain"), "{json}");
            assert!(!json.contains("by_checked_argument_return\""), "{json}");
        }
    }
}

#[test]
fn checked_function_membership_preserves_domains_falsehood_and_rollback() {
    for detail in [
        OutputDetail::Compact,
        OutputDetail::Normal,
        OutputDetail::Detailed,
    ] {
        for source in [
            "forall a seq(R),u fn(k N+) C,n N+:\n    $has_seq_limit(a,u(n+1)+1)\n    =>:\n        $has_seq_limit(a,u(n+1)+1)\n",
            "forall a,u seq(R),n N+:\n    $has_seq_limit(a,u(n+1)+1)\n",
            "forall u seq(R),n R:\n    u(n+1)+1<=u(n+1)+1\n",
            "forall f fn(x R:x>0) R,t R:\n    f(t)+1<=f(t)+1\n",
            "forall f fn(x R) C,t R:\n    f(t)+1<=f(t)+1\n",
            "forall u seq(R),n N+:\n    (u(n+1)+1)/u(n+1) $in R\n",
            "forall u seq(R),n N+:\n    u(n+1)+1<u(n+1)+1\n",
            include_str!(
                "../../../../examples/wd_negative/checked_function_order_alternative_guard.lit"
            ),
            "forall f fn(x R:x>0) R,g fn(x R) R,t R:\n    f(g(t))+1<=f(g(t))+1\n",
        ] {
            let mut rt = with_detail(detail);
            let before = memory_sizes(&rt);
            let result = rt.run_litex_code(source).unwrap();
            assert!(
                result.session_error.is_none(),
                "{detail:?}: {source}: {:?}",
                result.session_error
            );
            assert!(!result.success, "{detail:?}: {source}");
            assert_eq!(
                memory_sizes(&rt),
                before,
                "failed source leaked state: {source}"
            );
            assert!(!rt.run_litex_code("0=1").unwrap().success);
        }
    }
}

#[test]
fn checked_membership_leaf_obeys_the_inherited_ceiling_and_publishes_nothing() {
    use crate::ast::obj::StandardSet;
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have f fn(x R) R\nhave a R")
            .unwrap()
            .success
    );
    let Fact::AtomicFact(crate::ast::fact::AtomicFact::InFact(member)) =
        fact(&mut rt, "(f(a)+1) $in R")
    else {
        panic!("membership")
    };
    assert!(!rt
        .verify_obj_well_definedness(&member.element, VerifyState::top_level())
        .unwrap()
        .is_failed());
    let before = memory_sizes(&rt);
    assert!(rt
        .search_membership_of_checked_object(
            &member.element,
            &StandardSet::R,
            VerifyState::new(VerifyStateLevel::Direct)
        )
        .is_none());
    let checked = rt
        .search_membership_of_checked_object(
            &member.element,
            &StandardSet::R,
            VerifyState::new(VerifyStateLevel::KnownSpecialProperty),
        )
        .expect("known-return leaf composes");
    let P::Add { left, .. } = checked.reason else {
        panic!("add carrier")
    };
    assert!(matches!(left.reason, P::FunctionReturn { .. }));
    assert_eq!(memory_sizes(&rt), before);
    let result = rt
        .verify_fact(
            &Fact::AtomicFact(crate::ast::fact::AtomicFact::InFact(member)),
            VerifyState::top_level(),
        )
        .unwrap();
    assert!(!result.is_failed());
    assert_eq!(memory_sizes(&rt), before);
}
