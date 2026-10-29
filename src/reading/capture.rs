use crate::ast::SourceLine;
use crate::prelude::*;
use crate::run::source_observer::SourceObserver;
use crate::tokenize::{TokenBlock, Tokenizer};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use super::capture_generated::{
    capture_ast__stmt__Stmt, capture_execute__exec_stmt_result__ExecStmtResult,
};
use super::helper::{digest, object, strings, text};

#[path = "fact_capture.rs"]
mod fact_capture;
#[path = "inference_capture.rs"]
mod inference_capture;
#[path = "mathematical_meaning.rs"]
mod mathematical_meaning;
#[path = "source_statements.rs"]
mod source_statements;
#[path = "well_defined_capture.rs"]
mod well_defined_capture;

/// One export's observations. It never writes to a Runtime or execution scope.
pub(super) struct Capture {
    pub sources: Vec<JsonValue>,
    pub statements: Vec<JsonValue>,
    pub facts: BTreeMap<String, JsonValue>,
    pub symbols: BTreeMap<String, JsonValue>,
    pub occurrences: Vec<JsonValue>,
    pub rules: BTreeMap<String, JsonValue>,
    pub scopes: Vec<JsonValue>,
    pub diagnostics: Vec<JsonValue>,
    pub current_line: usize,
    pub subject_depth: usize,
    pub source_snapshot_depth: usize,
    evidence_nodes: Vec<JsonValue>,
    evidence_index: BTreeMap<String, String>,
    statement_rules: BTreeSet<String>,
    inferences: Vec<JsonValue>,
    well_definedness: BTreeMap<String, JsonValue>,
    wd_uses: BTreeSet<String>,
    current_source: String,
    current_path: String,
    current_statement: String,
    current_scope: String,
    root_scope: String,
    capturing_ast: bool,
    mentions: Vec<(usize, String, String, bool, String)>,
    citations: BTreeSet<String>,
    stores: BTreeSet<String>,
    missing: BTreeSet<String>,
    source_paths: BTreeMap<String, String>,
    configurations: BTreeMap<String, JsonValue>,
    entry_path: Option<String>,
    base_path: std::path::PathBuf,
    source_statements: source_statements::SourceStatements,
    language: OutputLanguage,
    pub proof_branch: Option<usize>,
    pub proof_part: String,
}

impl Capture {
    pub fn new(base_path: &Path, language: OutputLanguage) -> Self {
        let catalogue = JsonValue::parse(include_str!("rule_catalogue_generated.json"))
            .expect("generated reading catalogue is JSON");
        let mut rules = BTreeMap::new();
        if let JsonValue::Array(entries) = catalogue {
            for entry in entries {
                let id = field_text(&entry, "id");
                rules.insert(id, entry);
            }
        }
        Self {
            language,
            sources: Vec::new(),
            statements: Vec::new(),
            facts: BTreeMap::new(),
            symbols: BTreeMap::new(),
            occurrences: Vec::new(),
            rules,
            scopes: Vec::new(),
            diagnostics: Vec::new(),
            current_line: 1,
            subject_depth: 0,
            current_source: String::new(),
            current_path: String::new(),
            current_statement: String::new(),
            source_snapshot_depth: 0,
            evidence_nodes: Vec::new(),
            evidence_index: BTreeMap::new(),
            statement_rules: BTreeSet::new(),
            inferences: Vec::new(),
            well_definedness: BTreeMap::new(),
            wd_uses: BTreeSet::new(),
            current_scope: String::new(),
            root_scope: String::new(),
            capturing_ast: false,
            mentions: Vec::new(),
            citations: BTreeSet::new(),
            stores: BTreeSet::new(),
            missing: BTreeSet::new(),
            source_paths: BTreeMap::new(),
            configurations: BTreeMap::new(),
            entry_path: None,
            base_path: base_path
                .canonicalize()
                .unwrap_or_else(|_| base_path.to_path_buf()),
            source_statements: source_statements::SourceStatements::default(),
            proof_branch: None,
            proof_part: String::new(),
        }
    }

    pub fn finish(mut self, success: bool, error: Option<String>, strict: bool) -> JsonValue {
        let language = self.language;
        self.annotate_inferred_facts();
        self.annotate_wd_coverage();
        let trust = self.annotate_trust_origins();
        let mut diagnostics = self.diagnostics;
        if let Some(error) = error {
            diagnostics.push(object(vec![
                ("kind", text("execution")),
                ("message", text(&error)),
            ]));
        }
        let entry = self
            .sources
            .iter()
            .find(|source| {
                self.entry_path
                    .as_ref()
                    .is_some_and(|path| field_text(source, "path") == *path)
            })
            .or_else(|| {
                self.sources
                    .iter()
                    .find(|source| field_text(source, "role") == "book")
            })
            .or_else(|| self.sources.first());
        let entry_id = entry
            .map(|source| text(&field_text(source, "id")))
            .unwrap_or(JsonValue::Null);
        let executable_id = super::helper::executable_digest()
            .map(|id| text(&id))
            .unwrap_or(JsonValue::Null);
        let input = self
            .sources
            .iter()
            .map(|source| {
                object(vec![
                    ("path", text(&field_text(source, "path"))),
                    ("digest", text(&field_text(source, "digest"))),
                    (
                        "configuration_id",
                        text(&field_text(source, "configuration_id")),
                    ),
                ])
            })
            .collect();
        let input_id = digest(&JsonValue::Array(input).stringify());
        let mut output = object(vec![
            ("kind", text("reading")),
            ("schema_version", text("2")),
            ("evidence_encoding", text("dag")),
            (
                "engine",
                object(vec![
                    ("name", text(crate::LITEX)),
                    ("version", text(env!("CARGO_PKG_VERSION"))),
                    ("executable_id", executable_id),
                ]),
            ),
            (
                "catalogue_id",
                text(&digest(include_str!("rule_catalogue_generated.json"))),
            ),
            ("input_digest", text(&input_id)),
            (
                "execution_policy",
                object(vec![("strict", JsonValue::Bool(strict))]),
            ),
            ("trust_summary", trust),
            ("language", text(language.as_str())),
            (
                "run_result",
                text(if success { "success" } else { "failure" }),
            ),
            ("entry_source_id", entry_id),
            (
                "configurations",
                JsonValue::Array(self.configurations.into_values().collect()),
            ),
            ("sources", JsonValue::Array(self.sources)),
            ("statements", JsonValue::Array(self.statements)),
            ("evidence_nodes", JsonValue::Array(self.evidence_nodes)),
            ("inferences", JsonValue::Array(self.inferences)),
            (
                "well_definedness",
                JsonValue::Array(self.well_definedness.into_values().collect()),
            ),
            (
                "facts",
                JsonValue::Array(self.facts.into_values().collect()),
            ),
            (
                "symbols",
                JsonValue::Array(self.symbols.into_values().collect()),
            ),
            ("occurrences", JsonValue::Array(self.occurrences)),
            (
                "rules",
                JsonValue::Array(self.rules.into_values().collect()),
            ),
            ("scopes", JsonValue::Array(self.scopes)),
            ("diagnostics", JsonValue::Array(diagnostics)),
        ]);
        let bundle_id = digest(&output.stringify());
        if let JsonValue::Object(fields) = &mut output {
            fields.insert("bundle_id".into(), text(&bundle_id));
        }
        output
    }

    pub fn set_entry_file(&mut self, path: &Path) {
        self.entry_path = Some(self.logical_path(path));
    }

    pub fn intern_evidence(&mut self, value: JsonValue) -> JsonValue {
        if self.capturing_ast {
            return value;
        }
        // Exact structural keys avoid treating a fingerprint collision as
        // proof identity. Children are references, keeping keys bounded.
        let key = value.stringify();
        let id = if let Some(id) = self.evidence_index.get(&key) {
            id.clone()
        } else {
            let id = format!("evidence{}", self.evidence_nodes.len());
            self.evidence_nodes
                .push(object(vec![("id", text(&id)), ("node", value)]));
            self.evidence_index.insert(key, id.clone());
            id
        };
        object(vec![
            ("kind", text("evidence_reference")),
            ("evidence_id", text(&id)),
        ])
    }

    pub fn enter_scope(&mut self) -> String {
        let previous = self.current_scope.clone();
        let id = format!("scope{}", self.scopes.len());
        self.scopes.push(object(vec![
            ("id", text(&id)),
            ("parent_id", text(&previous)),
            ("statement_id", text(&self.current_statement)),
        ]));
        self.current_scope = id;
        previous
    }

    pub fn leave_scope(&mut self, previous: String) {
        self.current_scope = previous;
    }

    pub fn index_environment(&mut self, environment: &ExecEnv, runtime: &Runtime) {
        self.index_well_definedness(environment);
        let mut facts = environment.facts.facts_by_id.iter().collect::<Vec<_>>();
        facts.sort_by_key(|(id, _)| id.value());
        for (_, fact) in facts {
            if !self.facts.contains_key(&fact.fact_id().to_string()) {
                self.subject(fact, runtime);
            }
        }
    }

    pub fn environment(&mut self, _environment: &ExecEnv, _runtime: &Runtime) -> JsonValue {
        object(vec![
            ("kind", text("scope")),
            ("scope_id", text(&self.current_scope)),
        ])
    }

    pub fn subject(&mut self, fact: &Fact, _runtime: &Runtime) {
        if self.capturing_ast {
            return;
        }
        let id = fact.fact_id().to_string();
        let mut entry = object(vec![
            ("id", text(&id)),
            ("text", text(&fact.readable_string())),
            ("scope_id", text(&self.current_scope)),
        ]);
        if let Some(line) = crate::json_output::reading_fact_source_line(fact) {
            let source_id = self.source_id(&line.origin);
            if let JsonValue::Object(fields) = &mut entry {
                fields.insert("source_id".into(), text(&source_id));
                fields.insert("line".into(), JsonValue::Number(line.line as f64));
            }
        }
        self.facts.entry(id).or_insert(entry);
    }

    pub fn fact_reference(&mut self, id: &FactId, runtime: &Runtime) -> JsonValue {
        let id_text = id.to_string();
        if let Some(fact) = runtime.fact_by_id_in_stack(*id) {
            self.subject(fact, runtime);
        }
        if !self.capturing_ast && self.subject_depth == 0 {
            self.citations.insert(id_text.clone());
        }
        object(vec![
            ("kind", text("fact_reference")),
            ("fact_id", text(&id_text)),
        ])
    }

    pub fn stored(&mut self, ids: &[FactId]) {
        for id in ids {
            if let Some(JsonValue::Object(fields)) = self.facts.get_mut(&id.to_string()) {
                // The actual environment owns visibility. A result containing
                // local_env can also finish by storing a conclusion outside it.
                if !self.capturing_ast
                    && fields.get("scope_id").and_then(|value| value.as_str().ok())
                        == Some(self.root_scope.as_str())
                {
                    self.stores.insert(id.to_string());
                }
                if fields.get("producer_statement_id").is_none() {
                    fields.insert(
                        "producer_statement_id".into(),
                        text(&self.current_statement),
                    );
                }
            }
        }
    }

    pub fn identifier_id(&mut self, id: &IdentifierId, _runtime: &Runtime) -> JsonValue {
        object(vec![
            ("kind", text("identifier_id")),
            ("id", text(&id.to_string())),
        ])
    }

    pub fn wd_reference(&mut self, id: &WellDefinednessId, _runtime: &Runtime) -> JsonValue {
        if !self.capturing_ast {
            self.wd_uses.insert(id.to_string());
        }
        object(vec![
            ("kind", text("well_definedness_reference")),
            ("id", text(&id.to_string())),
        ])
    }

    pub fn source_line(&mut self, line: &SourceLine, _runtime: &Runtime) -> JsonValue {
        let source_id = self.source_id(&line.origin);
        object(vec![
            ("source_id", text(&source_id)),
            ("line", JsonValue::Number(line.line as f64)),
        ])
    }

    pub fn code_source(&mut self, source: &CodeSource, _runtime: &Runtime) -> JsonValue {
        text(&self.source_id(source))
    }

    pub fn bound_name(&mut self, name: &BoundName, runtime: &Runtime) -> JsonValue {
        let identifier = runtime.identifier_obj_for_stored_mention(name);
        self.symbol(&identifier, true, runtime)
    }

    pub fn identifier(&mut self, identifier: &IdentifierObj, runtime: &Runtime) -> JsonValue {
        self.symbol(identifier, false, runtime)
    }

    pub fn atomic_name(&mut self, name: &AtomicName, runtime: &Runtime) -> JsonValue {
        let (key, display) = match name {
            AtomicName::Plain { name } => (self.named_source_key(name), name.clone()),
            AtomicName::WithExportFileId {
                export_file_id,
                name,
            } => {
                let path = export_path(runtime, None, *export_file_id);
                (
                    format!("named:{}:{name}", self.logical_path(&path)),
                    name.clone(),
                )
            }
            AtomicName::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => {
                let path = export_path(runtime, Some(*global_mod_id), *export_file_id);
                (
                    format!("named:{}:{name}", self.logical_path(&path)),
                    name.clone(),
                )
            }
        };
        self.record_symbol(&key, &display, false);
        object(vec![
            ("kind", text("symbol_reference")),
            ("symbol_id", text(&key)),
            ("name", text(&display)),
        ])
    }

    pub fn named_definition(&mut self, name: &str, kind: &str, runtime: &Runtime) -> JsonValue {
        let resolved = runtime.atomic_name_for_plain_prop_ref(name.into());
        if self.capturing_ast && matches!(resolved, AtomicName::Plain { .. }) {
            self.register_named_binding(name);
        }
        let reference = self.atomic_name(&resolved, runtime);
        if self.capturing_ast {
            if let Some(mention) = self.mentions.last_mut() {
                mention.3 = true;
            }
        }
        let id = field_text(&reference, "symbol_id");
        if let Some(JsonValue::Object(fields)) = self.symbols.get_mut(&id) {
            fields.insert("kind".into(), text(kind));
            if self.capturing_ast {
                fields.insert(
                    "definition_statement_id".into(),
                    text(&self.current_statement),
                );
            }
        }
        reference
    }

    pub fn standard_set(&mut self, set: &StandardSet, _runtime: &Runtime) -> JsonValue {
        let name = Obj::StandardSet(set.clone()).readable_string();
        let key = format!("builtin:set:{name}");
        self.record_symbol(&key, &name, false);
        if let Some(JsonValue::Object(fields)) = self.symbols.get_mut(&key) {
            fields.insert("kind".into(), text("builtin"));
        }
        object(vec![
            ("kind", text("symbol_reference")),
            ("symbol_id", text(&key)),
            ("name", text(&name)),
        ])
    }

    pub fn unavailable(&mut self, type_name: &str) -> JsonValue {
        self.missing.insert(type_name.into());
        object(vec![
            ("kind", text("unavailable")),
            ("type", text(type_name)),
        ])
    }

    pub fn rule_application(
        &mut self,
        output: &mut JsonValue,
        id: &str,
        name: &str,
        message: &str,
    ) {
        self.statement_rules.insert(id.into());
        if let JsonValue::Object(fields) = output {
            fields.insert("rule_id".into(), text(id));
        }
        let rule = self
            .rules
            .entry(id.into())
            .or_insert_with(|| object(vec![("id", text(id))]));
        if let JsonValue::Object(fields) = rule {
            fields.insert("name".into(), text(name));
            fields.insert("message".into(), text(message));
        }
    }

    /// Attach copy to this application, not merely its family catalogue entry:
    /// several typed subrules can share a catalogue identity but have distinct laws.
    pub fn rule_comments(
        &self,
        output: &mut JsonValue,
        english: crate::json_output::explain::BuiltinRuleText,
        chinese: crate::json_output::explain::BuiltinRuleText,
    ) {
        let label = |copy: crate::json_output::explain::BuiltinRuleText| {
            object(vec![
                ("name", text(&copy.rule_name)),
                ("message", text(&copy.message)),
            ])
        };
        if let JsonValue::Object(fields) = output {
            fields.insert(
                "comment".into(),
                object(vec![("en", label(english)), ("zh", label(chinese))]),
            );
        }
    }

    fn symbol(
        &mut self,
        identifier: &IdentifierObj,
        definition: bool,
        runtime: &Runtime,
    ) -> JsonValue {
        let (key, name) = match identifier {
            IdentifierObj::Plain { id, name } => (format!("local:{id}"), name.clone()),
            IdentifierObj::WithExportFileId {
                export_file_id,
                name,
            } => {
                let path = export_path(runtime, None, *export_file_id);
                (
                    format!("export:{}:{name}", self.logical_path(&path)),
                    name.clone(),
                )
            }
            IdentifierObj::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => {
                let path = export_path(runtime, Some(*global_mod_id), *export_file_id);
                (
                    format!("export:{}:{name}", self.logical_path(&path)),
                    name.clone(),
                )
            }
        };
        self.record_symbol(&key, &name, definition);
        object(vec![
            ("kind", text("symbol_reference")),
            ("symbol_id", text(&key)),
            ("name", text(&name)),
        ])
    }

    fn record_symbol(&mut self, key: &str, name: &str, definition: bool) {
        self.symbols
            .entry(key.into())
            .or_insert_with(|| object(vec![("id", text(key)), ("name", text(name))]));
        if self.capturing_ast {
            self.mentions.push((
                self.current_line,
                key.into(),
                name.into(),
                definition,
                self.current_statement.clone(),
            ));
        }
    }

    fn source_id(&self, source: &CodeSource) -> String {
        let path = self.logical_path(&source.display_path());
        self.source_paths.get(&path).cloned().unwrap_or(path)
    }

    fn logical_path(&self, path: &Path) -> String {
        let absolute = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        match absolute.strip_prefix(&self.base_path) {
            Ok(path) => path.to_string_lossy().replace('\\', "/"),
            Err(_) => format!(
                "dependencies/{}/{}",
                digest(&absolute.parent().unwrap_or(&absolute).to_string_lossy()).replace(':', "-"),
                absolute.file_name().unwrap_or_default().to_string_lossy()
            ),
        }
    }

    fn map_occurrences(&mut self, block: &TokenBlock) -> bool {
        let mut tokens = BTreeMap::new();
        collect_tokens(block, &mut tokens);
        let mut cursors = BTreeMap::<usize, usize>::new();
        let mut complete = true;
        for (line, key, name, definition, statement_id) in self.mentions.clone() {
            let Some(entries) = tokens.get(&line) else {
                complete = false;
                continue;
            };
            let cursor = cursors.entry(line).or_default();
            let found = entries
                .iter()
                .enumerate()
                .skip(*cursor)
                .find(|(_, (token, _, _))| token == &name);
            let Some((index, (_, start, end))) = found else {
                complete = false;
                continue;
            };
            *cursor = index + 1;
            self.occurrences.push(object(vec![
                ("symbol_id", text(&key)),
                ("source_id", text(&self.current_source)),
                ("statement_id", text(&statement_id)),
                ("start_byte", JsonValue::Number(*start as f64)),
                ("end_byte", JsonValue::Number(*end as f64)),
                ("definition", JsonValue::Bool(definition)),
            ]));
        }
        complete
    }
}

impl SourceObserver for Capture {
    fn requires_source_evidence(&self) -> bool {
        true
    }

    fn source(&mut self, runtime: &Runtime, code: &str) {
        let path = self.logical_path(&runtime.current_file.display_path());
        let id = format!("source{}", self.sources.len());
        self.source_paths.insert(path.clone(), id.clone());
        self.current_path = path.clone();
        self.current_source = id.clone();
        self.current_scope = format!("file:{id}");
        self.root_scope = self.current_scope.clone();
        self.scopes.push(object(vec![
            ("id", text(&self.current_scope)),
            ("source_id", text(&id)),
            ("parent_id", JsonValue::Null),
        ]));
        let config = runtime
            .global_module_manager
            .current_litex_config()
            .expect("running source has a module configuration");
        let configuration = object(vec![
            (
                "imports",
                JsonValue::Array(
                    config
                        .imports
                        .iter()
                        .map(|import| {
                            object(vec![
                                ("alias", text(&import.alias)),
                                ("path", text(&self.logical_path(&import.path))),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "exports",
                JsonValue::Array(
                    config
                        .exports
                        .iter()
                        .map(|export| {
                            object(vec![
                                ("name", text(&export.name)),
                                ("path", text(&self.logical_path(&export.path))),
                            ])
                        })
                        .collect(),
                ),
            ),
        ]);
        let configuration_id = digest(&configuration.stringify());
        self.configurations
            .entry(configuration_id.clone())
            .or_insert_with(|| {
                object(vec![
                    ("id", text(&configuration_id)),
                    ("configuration", configuration),
                ])
            });
        let role = if matches!(runtime.current_file, CodeSource::ImportedExport { .. }) {
            "dependency"
        } else {
            "book"
        };
        // Reuse the language tokenizer, including comment removal and Unicode
        // normalization. These spans describe presentation, not proof state.
        let mut source_tokens = BTreeMap::new();
        if let Ok(blocks) = Tokenizer::new().tokenize(code, runtime.current_file.clone()) {
            for block in &blocks {
                collect_tokens(block, &mut source_tokens);
            }
        }
        let tokens = source_tokens
            .into_values()
            .flatten()
            .map(|(token, start, end)| {
                object(vec![
                    ("text", text(&token)),
                    ("start_byte", JsonValue::Number(start as f64)),
                    ("end_byte", JsonValue::Number(end as f64)),
                ])
            })
            .collect();
        let mut source = object(vec![
            ("id", text(&id)),
            ("path", text(&path)),
            ("content", text(code)),
            ("tokens", JsonValue::Array(tokens)),
            ("digest", text(&digest(code))),
            ("role", text(role)),
            ("configuration_id", text(&configuration_id)),
        ]);
        if let Some(titles) = super::helper::source_titles(&runtime.current_file.display_path()) {
            if let JsonValue::Object(fields) = &mut source {
                fields.insert("titles".into(), titles);
            }
        }
        self.sources.push(source);
    }

    fn statement(
        &mut self,
        runtime: &Runtime,
        block: &TokenBlock,
        statement: &Stmt,
        result: &ExecStmtResult,
    ) {
        let first = self.statements.len();
        self.prepare_source_statements(block);
        self.current_statement.clear();
        self.current_line = block.line;
        self.citations.clear();
        self.wd_uses.clear();
        self.stores.clear();
        self.missing.clear();
        self.mentions.clear();
        self.capturing_ast = true;
        let _ast = capture_ast__stmt__Stmt(statement, self, runtime);
        self.capturing_ast = false;
        for environment in &runtime.execution_environments_stack {
            self.index_environment(environment, runtime);
        }
        self.capture_source_result(first, result, runtime);
        let mapped = self.map_occurrences(block);
        self.finish_source_statements(first, mapped);
    }

    fn completed(&mut self, _runtime: &Runtime, result: &RunLitexCodeResult) {
        if let Some(error) = &result.session_error {
            self.diagnostics.push(object(vec![
                ("source_id", text(&self.current_source)),
                ("kind", text("termination")),
                ("message", text(&error.to_string())),
            ]));
        }
    }

    fn source_error(&mut self, _runtime: &Runtime, error: &RuntimeError) {
        let mut fields = vec![
            ("source_id", text(&self.current_source)),
            ("kind", text("source")),
            ("message", text(&error.to_string())),
        ];
        if let RuntimeError::ParseError(parse) = error {
            fields.push(("phase", text("parse")));
            fields.push(("summary", text(&parse.message)));
            fields.push(("line", JsonValue::Number(parse.line as f64)));
            if let Some(source) = &parse.source {
                fields.push(("line_text", text(&source.text)));
                if let Some(column) = source.column {
                    fields.push(("column", JsonValue::Number(column as f64)));
                }
            }
        }
        self.diagnostics.push(object(fields));
    }
}

fn field_text(value: &JsonValue, name: &str) -> String {
    value
        .as_object()
        .ok()
        .and_then(|fields| fields.get(name))
        .and_then(|value| value.as_str().ok())
        .unwrap_or("")
        .into()
}

fn collect_tokens(block: &TokenBlock, output: &mut BTreeMap<usize, Vec<(String, usize, usize)>>) {
    for (token, span) in block.header.iter().zip(&block.token_spans) {
        let line = block
            .source
            .as_ref()
            .map(|source| {
                source[..span.start]
                    .bytes()
                    .filter(|byte| *byte == b'\n')
                    .count()
                    + 1
            })
            .unwrap_or(block.line);
        output
            .entry(line)
            .or_default()
            .push((token.clone(), span.start, span.end));
    }
    for child in &block.body {
        collect_tokens(child, output);
    }
}

fn export_path(runtime: &Runtime, module: Option<usize>, export: usize) -> std::path::PathBuf {
    let config = match module {
        Some(module) => runtime
            .global_module_manager
            .imports()
            .get(module)
            .map(|module| &module.litex_config),
        None => Some(runtime.global_module_manager.litex_config()),
    };
    config
        .and_then(|config| config.exports.get(export))
        .map(|export| export.path.clone())
        .unwrap_or_default()
}
