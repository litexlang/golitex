use super::*;

#[test]
fn source_origin_separates_real_files_from_virtual_sources() {
    let mut module = ModuleRunner::new(
        ModuleId::ROOT,
        String::new(),
        ModuleLocation::Virtual,
        ProjectHierarchy::Module,
        None,
        ModuleStatus::Loaded,
    );
    let virtual_id = module.create_virtual_source(VirtualSource::Session);
    let named_virtual_id = module.create_virtual_source(VirtualSource::Named(
        "stmt-result-to-lean release-thm projection".to_string(),
    ));
    let real_id = module.create_real_source("/tmp/example.lit", None);

    assert!(matches!(
        &module.source(virtual_id).expect("virtual source").origin,
        SourcePath::VirtualSource(VirtualSource::Session)
    ));
    assert!(module
        .source(virtual_id)
        .expect("virtual source")
        .real_file_path()
        .is_none());
    assert_eq!(
        module
            .source(named_virtual_id)
            .expect("named virtual source")
            .display_label(),
        "stmt-result-to-lean release-thm projection"
    );
    assert!(module
        .source(named_virtual_id)
        .expect("named virtual source")
        .real_file_path()
        .is_none());
    assert_eq!(
        module.source_id_by_real_file_path(&RealFilePath::new("/tmp/example.lit")),
        Some(real_id)
    );
    assert_eq!(module.source_id_by_real_path("session"), None);
}
