use crate::prelude::*;

#[test]
fn source_codec_requires_the_real_path_and_preserves_all_variants() {
    for source in [
        CodeSource::Eval,
        CodeSource::Repl,
        CodeSource::Real("standalone.lit".into()),
        CodeSource::RootExport {
            path: "root.lit".into(),
            export_file_id: 1,
        },
        CodeSource::ImportedExport {
            path: "lib/base.lit".into(),
            global_mod_id: 2,
            export_file_id: 1,
        },
    ] {
        let encoded = super::def_prop_codec::encode_code_source(&source).unwrap();
        assert_eq!(
            super::def_prop_codec::decode_code_source(&encoded).unwrap(),
            source
        );
    }
    for old in [
        r#"{"tag":"StandaloneFile"}"#,
        r#"{"tag":"RootExport","export_file_id":0}"#,
    ] {
        let json = crate::knowledge_base::JsonValue::parse(old).unwrap();
        assert!(super::def_prop_codec::decode_code_source(&json).is_err());
    }
}
