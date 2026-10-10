use crate::prelude::*;

fn runtime(source: CodeSource) -> Runtime {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: true,
        strict: true,
        language: OutputLanguage::English,
    });
    rt.abort_source();
    rt.begin_source(source);
    assert!(rt.run_litex_code("prop lies_in(X set, S power_set(X)):\n    S $subset X\ntemplate<X set>:\n    have Subsets set = {S power_set(X): $lies_in(X, S)}").unwrap().success);
    rt.current_file = CodeSource::Repl;
    rt
}

#[test]
fn continued_export_repl_lookup_projects_the_original_refined_property() {
    let mut rt = runtime(CodeSource::RootExport {
        path: "prefix.lit".into(),
        export_file_id: 0,
    });
    let result = rt
        .run_litex_code(
            "thm member_has_property:\n    ? forall X set, S \\Subsets<X>:\n        $lies_in(X, S)",
        )
        .unwrap();
    assert!(
        result.success && result.session_error.is_none(),
        "{:?}",
        result.session_error
    );
    assert_eq!(rt.current_file, CodeSource::Repl);
}

#[test]
fn continued_export_repl_lookup_does_not_borrow_another_owner() {
    let rt = runtime(CodeSource::RootExport {
        path: "prefix.lit".into(),
        export_file_id: 0,
    });
    assert!(rt
        .def_prop_visible(&AtomicName::WithExportFileId {
            export_file_id: 0,
            name: "lies_in".into()
        })
        .is_some());
    assert!(rt
        .def_prop_visible(&AtomicName::WithExportFileId {
            export_file_id: 1,
            name: "lies_in".into()
        })
        .is_none());
    let rt = runtime(CodeSource::ImportedExport {
        path: "prefix.lit".into(),
        global_mod_id: 7,
        export_file_id: 0,
    });
    assert!(rt
        .def_prop_visible(&AtomicName::WithModAndExportFileId {
            global_mod_id: 7,
            export_file_id: 0,
            name: "lies_in".into()
        })
        .is_some());
    assert!(rt
        .def_prop_visible(&AtomicName::WithModAndExportFileId {
            global_mod_id: 8,
            export_file_id: 0,
            name: "lies_in".into()
        })
        .is_none());
    assert!(rt
        .def_prop_visible(&AtomicName::WithExportFileId {
            export_file_id: 0,
            name: "lies_in".into()
        })
        .is_none());
}
