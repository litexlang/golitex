use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{ExecFactStmtResult, VerifyState};
use crate::execute::ExecStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language: OutputLanguage::English })
}

#[test]
fn builtin_choice_definition_reuses_checked_pointwise_source() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have fn g_choice(alpha {1}) power_set({1}) = {1}\nhave fn f_choice(alpha {1}) {1} = 1\nforall alpha {1}:\n    f_choice(alpha) $in g_choice(alpha)\n").unwrap();
    assert!(run.success);
    let tokens = Tokenizer::new().tokenize("$is_choice_function_for({1}, power_set({1}), g_choice, f_choice)", rt.current_file.clone()).unwrap();
    let goal = rt.parse(&tokens).unwrap().remove(0);
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::IsChoiceFunctionForFact(goal))) = goal else { panic!("choice fact"); };
    let requirements = rt.choice_definition_requirements(&goal).unwrap();
    for requirement in requirements {
        let proof = rt.verify_fact(&requirement, VerifyState::top_level()).unwrap();
        if proof.is_failed() {
            let result = ExecStmtResult::Fact(ExecFactStmtResult::Failed(proof));
            panic!("{}\n{}", requirement.ir(), crate::json_output::project_stmt_detailed(&result, &rt).stringify());
        }
    }
    let run = rt.run_litex_code("by def $is_choice_function_for({1}, power_set({1}), g_choice, f_choice)\n").unwrap();
    assert!(run.success, "{}", crate::json_output::emit_run_detailed(&run, &rt, "test", None));
}
