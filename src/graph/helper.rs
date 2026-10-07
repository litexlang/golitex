use crate::ast::line_file::SourceLine;
use crate::ast::fact::{Fact, AtomicFact};
use crate::knowledge_base::JsonValue;
use crate::runtime::{CodeSource, Runtime};

pub(super) fn object(fields: Vec<(&str, JsonValue)>) -> JsonValue {
    JsonValue::object_from(fields.into_iter().map(|(key, value)| (key.into(), value)).collect())
}

pub(super) fn string(value: impl Into<String>) -> JsonValue {
    JsonValue::String(value.into())
}

pub(super) fn source_path(line: &SourceLine, runtime: &Runtime, fallback: &str) -> String {
    let manager = &runtime.global_module_manager;
    let path = match &line.origin {
        CodeSource::RootExport { export_file_id } => manager.litex_config().exports.get(*export_file_id).map(|file| &file.path),
        CodeSource::ImportedExport { global_mod_id, export_file_id } => manager.imports().get(*global_mod_id)
            .and_then(|module| module.litex_config.exports.get(*export_file_id)).map(|file| &file.path),
        CodeSource::Eval | CodeSource::Repl | CodeSource::StandaloneFile => None,
    };
    path.map(|path| path.display().to_string()).unwrap_or_else(|| fallback.into())
}

pub(super) fn file_scope(origin: &CodeSource, source: &str) -> String {
    let owner = match origin {
        CodeSource::RootExport { export_file_id } => format!("root:{export_file_id}"),
        CodeSource::ImportedExport { global_mod_id, export_file_id } => format!("module:{global_mod_id}:{export_file_id}"),
        CodeSource::Eval => "eval".into(),
        CodeSource::Repl => "repl".into(),
        CodeSource::StandaloneFile => "standalone".into(),
    };
    format!("file:{owner}:{source}")
}

pub(super) fn fact_line(fact: &Fact) -> Option<&SourceLine> {
    match fact {
        Fact::AtomicFact(atomic) => atomic_source_line(atomic),
        Fact::ExistFact(f) | Fact::ExistUniqueFact(f) | Fact::NotExistFact(f) => f.line_file.as_ref(),
        Fact::AndFact(f) => f.line_file.as_ref(),
        Fact::ChainFact(f) => f.line_file.as_ref(),
        Fact::OrFact(f) => f.line_file.as_ref(),
        Fact::ForallFact(f) => f.line_file.as_ref(),
        Fact::ForallFactWithIff(f) => f.line_file.as_ref(),
        Fact::NotForall(f) => f.line_file.as_ref(),
    }
}

fn atomic_source_line(fact: &AtomicFact) -> Option<&SourceLine> {
    match fact {
        AtomicFact::NormalAtomicFact(f) => f.line_file.as_ref(),
        AtomicFact::NotNormalAtomicFact(f) => f.line_file.as_ref(),
        AtomicFact::EqualFact(f) => f.line_file.as_ref(),
        AtomicFact::NotEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::LessFact(f) => f.line_file.as_ref(),
        AtomicFact::GreaterFact(f) => f.line_file.as_ref(),
        AtomicFact::LessEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::GreaterEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::IsSetFact(f) => f.line_file.as_ref(),
        AtomicFact::IsNonemptySetFact(f) => f.line_file.as_ref(),
        AtomicFact::IsFiniteSetFact(f) => f.line_file.as_ref(),
        AtomicFact::InFact(f) => f.line_file.as_ref(),
        AtomicFact::SubsetFact(f) => f.line_file.as_ref(),
        AtomicFact::SupersetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotLessFact(f) => f.line_file.as_ref(),
        AtomicFact::NotGreaterFact(f) => f.line_file.as_ref(),
        AtomicFact::NotLessEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::NotGreaterEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsSetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsNonemptySetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsFiniteSetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotInFact(f) => f.line_file.as_ref(),
        AtomicFact::NotSubsetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotSupersetFact(f) => f.line_file.as_ref(),
        AtomicFact::ProperSubsetFact(f) => f.line_file.as_ref(),
        AtomicFact::ProperSupersetFact(f) => f.line_file.as_ref(),
        AtomicFact::PrimeFact(f) => f.line_file.as_ref(),
        AtomicFact::CoprimeFact(f) => f.line_file.as_ref(),
        AtomicFact::DvdFact(f) => f.line_file.as_ref(),
        AtomicFact::InjectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::SurjectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::BijectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::IsChoiceFunctionForFact(f) => f.line_file.as_ref(),
        AtomicFact::NotProperSubsetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotProperSupersetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotPrimeFact(f) => f.line_file.as_ref(),
        AtomicFact::NotCoprimeFact(f) => f.line_file.as_ref(),
        AtomicFact::NotDvdFact(f) => f.line_file.as_ref(),
        AtomicFact::NotInjectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::NotSurjectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::NotBijectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsChoiceFunctionForFact(f) => f.line_file.as_ref(),
    }
}
