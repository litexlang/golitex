use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

const IFF: &str =
    include_str!("../../../../examples/test_statements/negative/def_thm_stmt/forall-iff-goal.lit");
const ACCEPTANCE: &str =
    include_str!("../../../../examples/stmt_nodes/definition/def_thm_forall_iff_boundary.lit");
const STRICT_ORDER_CONTEXT: &str = r"
prop partial_order_laws(s set, le_rel power_set(cart(s, s))):
    forall x s:
        (x, x) $in le_rel
    forall x, y, z s:
        (x, y) $in le_rel
        (y, z) $in le_rel
        =>:
            (x, z) $in le_rel
    forall x, y s:
        (x, y) $in le_rel
        (y, x) $in le_rel
        =>:
            x = y

template<s set>:
    have PartialOrder set = {le_rel power_set(cart(s, s)): $partial_order_laws(s, le_rel)}

prop is_less_than_in_order(A set, order \PartialOrder<A>, x, y A):
    (x, y) $in order
    x != y
";

#[test]
fn quantified_iff_is_a_user_failure_in_normal_and_detailed_output() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = runtime(language);
        let run = rt.run_litex_code(IFF).unwrap();
        assert!(!run.success && run.session_error.is_none());
        assert_eq!(run.statement_results.len(), 1);
        assert!(rt.def_thm_visible_in_stack("equality_iff").is_none());
        for json in [
            crate::json_output::project_stmt_normal(&run.statement_results[0], &rt),
            crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt),
        ] {
            let text = json.stringify();
            assert!(text.contains("goal_unsupported"), "{text}");
            assert!(
                text.contains("thm: forall ... <=> goals are not supported"),
                "{text}"
            );
            assert!(!text.contains("internal_bug"), "{text}");
        }
    }
}

#[test]
fn unsupported_goal_rejects_before_wd_or_proof_body() {
    let mut rt = runtime(OutputLanguage::English);
    let run = rt.run_litex_code(
        "thm bad:\n    ? forall x R:\n        =>:\n            1 / 0 = 1 / 0\n        <=>:\n            x = x\n    have leaked R = 0\n",
    ).unwrap();
    assert!(!run.success && run.session_error.is_none());
    let text =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(text.contains("goal_unsupported"), "{text}");
    assert!(!text.contains("goal_well_defined"), "{text}");
    assert!(rt.def_thm_visible_in_stack("bad").is_none());
    assert!(!rt.run_litex_code("leaked = 0").unwrap().success);
}

#[test]
fn rejected_theorem_can_be_corrected_in_the_same_runtime() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(!rt.run_litex_code(IFF).unwrap().success);
    let corrected = rt.run_litex_code("thm equality_iff:\n    ? forall x, y R:\n        x = y\n        =>:\n            y = x\n").unwrap();
    assert!(corrected.success && corrected.session_error.is_none());
    assert!(
        rt.run_litex_code("by thm equality_iff(1, 1) => 1 = 1")
            .unwrap()
            .success
    );
    assert!(rt.run_litex_code(ACCEPTANCE).unwrap().success);
    let false_goal = rt
        .run_litex_code("thm false_goal:\n    ? forall x R:\n        x != x\n")
        .unwrap();
    assert!(!false_goal.success && false_goal.session_error.is_none());
}

#[test]
fn strict_order_dependent_iff_also_stops_at_the_input_boundary() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(rt.run_litex_code(STRICT_ORDER_CONTEXT).unwrap().success);
    let run = rt.run_litex_code("thm strict_order_iff:\n    ? forall A set, order \\PartialOrder<A>, x, y A:\n        =>:\n            $is_less_than_in_order(A, order, x, y)\n        <=>:\n            (x, y) $in order\n            x != y\n").unwrap();
    assert!(!run.success && run.session_error.is_none());
    let text = crate::json_output::project_stmt_normal(&run.statement_results[0], &rt).stringify();
    assert!(text.contains("goal_unsupported"), "{text}");
}

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}
