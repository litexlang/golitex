use crate::ast::obj::IdentifierObj;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{CodeSource, RealOrVirtualPath, Runtime};

fn runtime(source: CodeSource) -> Runtime {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    rt.finish_file();
    rt.set_code_source(source);
    rt.begin_file(RealOrVirtualPath::Eval);
    rt
}

fn sources() -> [CodeSource; 3] {
    [
        CodeSource::StandaloneFile,
        CodeSource::RootExport { export_file_id: 0 },
        CodeSource::ImportedExport {
            global_mod_id: 0,
            export_file_id: 0,
        },
    ]
}

#[test]
fn scalar_witness_retains_outer_identity_under_same_named_exist_binder() {
    for source in sources() {
        let mut rt = runtime(source);
        let run = rt
            .run_litex_code(include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/examples/wd/witness_same_named_binder.lit"
            )))
            .unwrap();
        assert!(
            run.success,
            "{}",
            crate::json_output::emit_run_detailed(&run, &rt, "same name", None)
        );
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn function_witness_retains_outer_identity_under_same_named_exist_binder() {
    for source in sources() {
        let mut rt = runtime(source);
        let run = rt.run_litex_code("prop has_fn_copy(f fn(x R) R):\n    exist step fn(x R) R st {step = f}\nhave fn step(x R) R = x + 1\nwitness $has_fn_copy(step) from step\nstep(2) = 3\n").unwrap();
        assert!(
            run.success,
            "{}",
            crate::json_output::emit_run_detailed(&run, &rt, "function witness", None)
        );
    }
}

#[test]
fn failed_same_named_witness_preserves_outer_definition_and_discards_local_facts() {
    for source in sources() {
        let mut rt = runtime(source);
        assert!(
            rt.run_litex_code("prop has_copy(a R):\n    exist g R st {g = a}\nhave g R = 2\n")
                .unwrap()
                .success
        );
        let sizes = |rt: &Runtime| {
            rt.execution_environments_stack
                .iter()
                .map(|e| {
                    (
                        e.facts.facts_by_id.len(),
                        e.definitions.identifiers.len(),
                        e.well_defined_objects.object_to_wd_id.len(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let before = sizes(&rt);
        let run = rt.run_litex_code("witness $has_copy(3) from g").unwrap();
        assert!(!run.success && run.session_error.is_none());
        assert_eq!(before, sizes(&rt));
        assert!(rt.run_litex_code("g = 2").unwrap().success);
        assert!(!rt.run_litex_code("g = 3").unwrap().success);
    }
}

#[test]
fn surface_name_does_not_validate_an_unrelated_binding_id() {
    let mut rt = runtime(CodeSource::StandaloneFile);
    assert!(
        rt.run_litex_code("have g R = 2\nhave j R = 3")
            .unwrap()
            .success
    );
    let g = IdentifierObj::Plain {
        name: "g".into(),
        id: rt.resolve_plain_atom("g").unwrap(),
    };
    let j_id = rt.resolve_plain_atom("j").unwrap();
    assert!(rt.stored_identifier_definition_visible(&g).is_some());
    let forged = IdentifierObj::Plain {
        name: "g".into(),
        id: j_id,
    };
    assert!(rt.stored_identifier_definition_visible(&forged).is_none());
}
