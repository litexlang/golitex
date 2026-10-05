use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{CodeSource, Runtime};

fn runtime(source: CodeSource) -> Runtime {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    rt.set_code_source(source);
    rt
}

fn rejected_binding(code: &str) {
    for source in [
        CodeSource::Eval,
        CodeSource::Repl,
        CodeSource::RootExport { export_file_id: 0 },
    ] {
        let mut rt = runtime(source);
        let run = rt.run_litex_code(code).unwrap();
        assert!(!run.success, "reserved binding accepted: {code}");
        let error = format!("{:?}", run.session_error);
        assert!(error.contains("reserved builtin name"), "{code}: {error}");
        assert!(!error.contains("internal_bug"));
        // Parse rejection must discard both the attempted name and any prefix.
        assert!(
            rt.run_litex_code("have fn picked(t R)R=t\npicked(2)=2\n")
                .unwrap()
                .success,
            "failed reserved declaration leaked its bindings: {code}"
        );
        assert!(!rt.run_litex_code("0=1\n").unwrap().success);
    }
}

#[test]
fn reserved_constants_and_object_forms_reject_declarations_before_use() {
    for name in [
        "i", "e", "pi", "N", "Z", "Q", "R", "C", "sin", "cos", "sqrt", "re", "img", "C_abs", "exp",
        "ln", "sum", "cart", "fn", "let",
    ] {
        rejected_binding(&format!("let {name}=0\n"));
        rejected_binding(&format!("forall {name} R:\n    {name}={name}\n"));
    }
}

#[test]
fn reserved_parameter_cannot_silently_become_a_constant_or_standard_set() {
    for code in [
        "have fn picked(e R)R=e\npicked(2)=e\n",
        "forall A,B,C set:\n    $is_nonempty_set(A) or $is_nonempty_set(B)\n    =>:\n        $is_nonempty_set(C)\n",
        "forall e R:\n    e>0\n",
        "exist e R st {e=e}\n",
        "have f fn(e R)R\n",
        "let f=fn(e R)R{e}\n",
        "forall U set:\n    {e U: e=e}={e U: e=e}\n",
        "template<e R>:\n    have picked R=e\n",
        "struct Box<e set>:\n    value e\n    tag N\n",
        "by induc e from 0:\n    ? e=e\n",
    ] { rejected_binding(code); }
}

#[test]
fn reserved_definition_field_witness_and_preimage_names_reject() {
    for code in [
        "struct Box:\n    i C\n    tag N\n",
        "have fn e(x R)R=x\n",
        "prop e(x R):\n    x=x\n",
        "abstract_prop p(e)\n",
        "thm e:\n    ? 0=0\n",
        "witness exist x R st {x=0} from 0\nobtain e from exist x R st {x=0}\n",
        "have fn identity(x R)R=x\nhave by fn_preimage: e from identity(0) $in fn_range(identity)\n",
    ] { rejected_binding(code); }
}

#[test]
fn builtin_uses_similar_names_and_failed_binding_reuse_remain_valid() {
    let code = include_str!("../../../examples/wd/reserved_object_bindings.lit");
    for source in [
        CodeSource::Eval,
        CodeSource::Repl,
        CodeSource::RootExport { export_file_id: 0 },
    ] {
        let mut rt = runtime(source);
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none());
        let normal = crate::json_output::emit_run_normal(&run, &rt, "reserved binding", None);
        let detailed = crate::json_output::emit_run_detailed(&run, &rt, "reserved binding", None);
        assert!(normal.contains("picked(2) = 2"));
        assert!(detailed.contains("picked"));
        assert!(!rt.run_litex_code("picked(2)=3\n").unwrap().success);
    }
}
