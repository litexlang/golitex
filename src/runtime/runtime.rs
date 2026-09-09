//! Run-wide runtime state and current-source lifecycle.

use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

/// Owns the mutable state for one top-level Litex invocation.
///
/// The runtime keeps module lookup, source activation, environments, IDs, and
/// invocation configuration together so nested execution never needs a second
/// runtime registry.
pub struct Runtime {
    /// Module registry and persistent source environments for this top-level
    /// run.
    pub module_manager: Box<ModuleManager>,

    /// Module that owns `current_source_id`.
    ///
    /// Source IDs are module-local because import targets carry their owner
    /// module ID. A Runtime is always source-bound; construction creates a
    /// registered virtual source before exposing the value.
    pub(crate) current_module_id: ModuleId,

    /// Source currently being parsed or executed.
    pub(crate) current_source_id: SourceId,

    /// Temporary environments nested inside the current source.
    pub execution_environments_stack: Vec<Box<ExecEnv>>,

    /// Transient binder and scope state shared by one nested parser traversal.
    ///
    /// Changing the current source neither consumes nor resets it.
    pub(crate) parse_context: ParseContext,

    /// Number of nested definition statements currently being parsed.
    ///
    /// Bare AtomicName references at a use site remain unqualified.  A
    /// definition body, however, records its local names with the owning
    /// module so the same stored theorem/definition can be used after import
    /// without guessing an imported module at the caller.
    pub(crate) parsing_definition_depth: usize,

    /// Monotone runtime-wide allocator for fact IDs.
    ///
    /// Local environments may disappear, but a fact ID is never reused during
    /// the run.
    pub next_fact_id: u64,

    /// Runtime-wide allocator for globally unique symbol IDs.
    pub symbol_id_allocator: Rc<SymbolIdAllocator>,

    /// Direct struct carriers learned when typed bindings execute.
    ///
    /// Exact transient binder identities remain usable after their local
    /// environment ends, for example when a stored theorem is instantiated.
    pub(crate) executed_direct_struct_carriers: HashMap<SymbolId, StructObj>,

    /// Verification, output, language, and summary settings for Litex execution.
    pub execution_options: LitexExecutionOptions,

    /// Whether the constructor-created virtual source is still available for
    /// the first explicit source selection.
    bootstrap_source_pending: bool,
}

/// Checkpoint used when temporarily activating another registered source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceActivation {
    /// Module that owns the checkpointed source id.
    pub module_id: ModuleId,

    /// Source that was active before a projection temporarily switched source.
    pub source_id: SourceId,

    /// Active verification mode restored with the source.
    pub mode: TrustedOrRequireVerify,
}

impl Runtime {
    pub fn new(execution_options: LitexExecutionOptions) -> Self {
        let mut module_manager = ModuleManager::new();
        let source_id = module_manager.create_virtual_root_module(VirtualSource::Eval);
        Runtime {
            module_manager: Box::new(module_manager),
            current_module_id: ModuleId::ROOT,
            current_source_id: source_id,
            execution_environments_stack: vec![],
            parse_context: ParseContext::new(),
            parsing_definition_depth: 0,
            next_fact_id: 1,
            symbol_id_allocator: Rc::new(SymbolIdAllocator::new()),
            executed_direct_struct_carriers: HashMap::new(),
            execution_options,
            bootstrap_source_pending: true,
        }
    }
}

fn virtual_source_from_legacy_label(label: &str) -> VirtualSource {
    match label.to_ascii_lowercase().as_str() {
        "eval" => VirtualSource::Eval,
        "repl" => VirtualSource::Repl,
        "session" => VirtualSource::Session,
        "to-lean" | "to_lean" => VirtualSource::ToLean,
        "to-latex" | "to_latex" => VirtualSource::ToLatex,
        _ => VirtualSource::Named(label.to_string()),
    }
}

impl Default for Runtime {
    fn default() -> Self {
        Self::new(LitexExecutionOptions::default())
    }
}

impl Runtime {
    pub fn allocate_fact_id(&mut self) -> Result<FactId, RuntimeError> {
        let value = self.next_fact_id;
        self.next_fact_id = value.checked_add(1).ok_or_else(|| {
            RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                "fact ID space exhausted".to_string(),
            )))
        })?;
        Ok(FactId::new(value))
    }

    /// Construct facts with IDs allocated exclusively by this Runtime.
    pub fn new_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<EqualFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(EqualFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_not_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<NotEqualFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotEqualFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_less_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<LessFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(LessFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_greater_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<GreaterFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(GreaterFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_less_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<LessEqualFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(LessEqualFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_greater_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<GreaterEqualFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(GreaterEqualFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_not_less_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<NotLessFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotLessFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_not_greater_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<NotGreaterFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotGreaterFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_not_less_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<NotLessEqualFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotLessEqualFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_not_greater_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<NotGreaterEqualFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotGreaterEqualFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_in_fact(
        &mut self,
        element: Obj,
        set: Obj,
        line_file: LineFile,
    ) -> Result<InFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(InFact {
            fact_id,
            element,
            set,
            line_file,
        })
    }

    pub fn new_not_in_fact(
        &mut self,
        element: Obj,
        set: Obj,
        line_file: LineFile,
    ) -> Result<NotInFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotInFact {
            fact_id,
            element,
            set,
            line_file,
        })
    }

    pub fn new_is_set_fact(
        &mut self,
        set: Obj,
        line_file: LineFile,
    ) -> Result<IsSetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(IsSetFact {
            fact_id,
            set,
            line_file,
        })
    }

    pub fn new_is_nonempty_set_fact(
        &mut self,
        set: Obj,
        line_file: LineFile,
    ) -> Result<IsNonemptySetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(IsNonemptySetFact {
            fact_id,
            set,
            line_file,
        })
    }

    pub fn new_is_finite_set_fact(
        &mut self,
        set: Obj,
        line_file: LineFile,
    ) -> Result<IsFiniteSetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(IsFiniteSetFact {
            fact_id,
            set,
            line_file,
        })
    }

    pub fn new_is_cart_fact(
        &mut self,
        set: Obj,
        line_file: LineFile,
    ) -> Result<IsCartFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(IsCartFact {
            fact_id,
            set,
            line_file,
        })
    }

    pub fn new_is_tuple_fact(
        &mut self,
        tuple: Obj,
        line_file: LineFile,
    ) -> Result<IsTupleFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(IsTupleFact {
            fact_id,
            set: tuple,
            line_file,
        })
    }

    pub fn new_not_is_set_fact(
        &mut self,
        set: Obj,
        line_file: LineFile,
    ) -> Result<NotIsSetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotIsSetFact {
            fact_id,
            set,
            line_file,
        })
    }

    pub fn new_not_is_nonempty_set_fact(
        &mut self,
        set: Obj,
        line_file: LineFile,
    ) -> Result<NotIsNonemptySetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotIsNonemptySetFact {
            fact_id,
            set,
            line_file,
        })
    }

    pub fn new_not_is_finite_set_fact(
        &mut self,
        set: Obj,
        line_file: LineFile,
    ) -> Result<NotIsFiniteSetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotIsFiniteSetFact {
            fact_id,
            set,
            line_file,
        })
    }

    pub fn new_not_is_cart_fact(
        &mut self,
        set: Obj,
        line_file: LineFile,
    ) -> Result<NotIsCartFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotIsCartFact {
            fact_id,
            set,
            line_file,
        })
    }

    pub fn new_not_is_tuple_fact(
        &mut self,
        tuple: Obj,
        line_file: LineFile,
    ) -> Result<NotIsTupleFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotIsTupleFact {
            fact_id,
            set: tuple,
            line_file,
        })
    }

    pub fn new_subset_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<SubsetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(SubsetFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_superset_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<SupersetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(SupersetFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_not_subset_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<NotSubsetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotSubsetFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_not_superset_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<NotSupersetFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotSupersetFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_fn_equal_in_fact(
        &mut self,
        left: Obj,
        right: Obj,
        set: Obj,
        line_file: LineFile,
    ) -> Result<FnEqualInFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(FnEqualInFact {
            fact_id,
            left,
            right,
            set,
            line_file,
        })
    }

    pub fn new_fn_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
    ) -> Result<FnEqualFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(FnEqualFact {
            fact_id,
            left,
            right,
            line_file,
        })
    }

    pub fn new_normal_atomic_fact(
        &mut self,
        predicate: AtomicName,
        body: Vec<Obj>,
        line_file: LineFile,
    ) -> Result<NormalAtomicFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NormalAtomicFact {
            fact_id,
            predicate,
            body,
            line_file,
        })
    }

    pub fn new_not_normal_atomic_fact(
        &mut self,
        predicate: AtomicName,
        body: Vec<Obj>,
        line_file: LineFile,
    ) -> Result<NotNormalAtomicFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotNormalAtomicFact {
            fact_id,
            predicate,
            body,
            line_file,
        })
    }

    pub fn new_not_forall_fact(
        &mut self,
        forall_fact: ForallFact,
    ) -> Result<NotForallFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(NotForallFact {
            fact_id,
            forall_fact,
        })
    }

    pub fn new_and_fact(
        &mut self,
        facts: Vec<AtomicFact>,
        line_file: LineFile,
    ) -> Result<AndFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(AndFact {
            fact_id,
            facts,
            line_file,
        })
    }

    pub fn new_or_fact(
        &mut self,
        facts: Vec<AndChainAtomicFact>,
        line_file: LineFile,
    ) -> Result<OrFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(OrFact {
            fact_id,
            facts,
            line_file,
        })
    }

    pub fn new_chain_fact(
        &mut self,
        objs: Vec<Obj>,
        prop_names: Vec<AtomicName>,
        line_file: LineFile,
    ) -> Result<ChainFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        Ok(ChainFact {
            fact_id,
            objs,
            prop_names,
            line_file,
        })
    }

    pub fn new_forall_fact(
        &mut self,
        typed_parameters: TypedParameterList,
        dom_facts: Vec<Fact>,
        then_facts: Vec<ExistOrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Result<ForallFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        let fact = ForallFact {
            fact_id,
            typed_parameters,
            dom_facts,
            then_facts,
            line_file,
        };
        check_forall_fact_has_no_duplicate_forall_free_parameter(&fact)?;
        Ok(fact)
    }

    pub fn new_forall_fact_with_iff(
        &mut self,
        forall_fact: ForallFact,
        iff_facts: Vec<ExistOrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Result<ForallFactWithIff, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        let fact = ForallFactWithIff {
            fact_id,
            forall_fact,
            iff_facts,
            line_file,
        };
        check_forall_fact_with_iff_has_no_duplicate_forall_free_parameter(&fact)?;
        Ok(fact)
    }

    pub fn new_plain_exist_fact(
        &mut self,
        typed_parameters: TypedParameterList,
        facts: Vec<QuantifierFreeFact>,
        line_file: LineFile,
    ) -> Result<PlainExistFact, RuntimeError> {
        let fact_id = self.allocate_fact_id()?;
        let fact = PlainExistFact {
            fact_id,
            typed_parameters,
            facts,
            line_file,
        };
        check_exist_fact_has_no_duplicate_exist_free_parameter(&ExistFact::PlainExistFact(
            fact.clone(),
        ))?;
        Ok(fact)
    }

    pub fn set_output_detail(&mut self, output_detail: OutputDetail) {
        self.execution_options.set_output_detail(output_detail);
    }

    pub fn effective_output_detail(&self) -> OutputDetail {
        self.execution_options.output_detail()
    }

    #[deprecated(note = "use `set_output_detail`")]
    pub fn set_output_style(&mut self, output_detail: OutputDetail) {
        self.set_output_detail(output_detail);
    }

    #[deprecated(note = "use `effective_output_detail`")]
    pub fn effective_output_style(&self) -> OutputDetail {
        self.effective_output_detail()
    }

    pub fn is_compact_output(&self) -> bool {
        self.effective_output_detail() == OutputDetail::Compact
    }

    pub fn is_normal_output(&self) -> bool {
        self.effective_output_detail() == OutputDetail::Normal
    }

    pub fn is_detailed_output(&self) -> bool {
        self.effective_output_detail() == OutputDetail::Detailed
    }

    pub fn current_file_path_rc(&self) -> Rc<str> {
        Rc::from(self.current_source().display_label())
    }

    pub fn current_source(&self) -> &Source {
        let module_id = self.current_module_id;
        let source_id = self.current_source_id;
        self.module_manager
            .module(module_id)
            .and_then(|module| module.source(source_id))
            .expect("current source should be registered")
    }

    fn activate_source(
        &mut self,
        module_id: ModuleId,
        source_id: SourceId,
        mode: TrustedOrRequireVerify,
    ) {
        assert!(
            self.execution_environments_stack.is_empty(),
            "a source cannot be selected with an active local environment"
        );
        assert!(
            self.module_manager
                .module(module_id)
                .and_then(|module| module.source(source_id))
                .is_some(),
            "a source can only be selected after it has been registered"
        );
        self.current_module_id = module_id;
        self.current_source_id = source_id;
        self.execution_options.trusted_or_require_verify = mode;
        self.bootstrap_source_pending = false;
    }

    pub fn source_activation(&self) -> SourceActivation {
        SourceActivation {
            module_id: self.current_module_id,
            source_id: self.current_source_id,
            mode: self.execution_options.trusted_or_require_verify,
        }
    }

    pub fn restore_source_activation(&mut self, activation: SourceActivation) {
        self.activate_source(activation.module_id, activation.source_id, activation.mode);
    }

    pub fn current_parse_context(&self) -> &ParseContext {
        &self.parse_context
    }

    pub fn current_parse_context_mut(&mut self) -> &mut ParseContext {
        &mut self.parse_context
    }

    pub fn current_module_id(&self) -> ModuleId {
        self.current_module_id
    }

    pub fn current_source_id(&self) -> SourceId {
        self.current_source_id
    }

    pub fn current_module(&self) -> &ModuleRunner {
        self.module_manager
            .module(self.current_module_id())
            .expect("current module should exist")
    }

    pub fn current_module_mut(&mut self) -> &mut ModuleRunner {
        let module_id = self.current_module_id();
        self.module_manager
            .module_mut(module_id)
            .expect("current module should exist")
    }

    pub fn activate_source_for_execution(&mut self, module_id: ModuleId, source_id: SourceId) {
        self.activate_source_with_mode(
            module_id,
            source_id,
            TrustedOrRequireVerify::RequireVerification,
        );
    }

    pub fn activate_source_with_mode(
        &mut self,
        module_id: ModuleId,
        source_id: SourceId,
        execution_mode: TrustedOrRequireVerify,
    ) {
        debug_assert!(
            self.parse_context.is_at_root_scope(),
            "a source cannot be selected inside an active parser scope"
        );
        self.activate_source(module_id, source_id, execution_mode);
    }

    pub fn canonical_module_name_for_parse(&self, name: &str) -> String {
        self.module_manager
            .canonical_name_for_reference(self.current_module_id, name)
            .unwrap_or_else(|| name.to_string())
    }

    pub fn strict_mode_applies_to_current_module(&self) -> bool {
        if !self.execution_options.is_strict() {
            return false;
        }
        !self
            .module_manager
            .module(self.current_module_id)
            .is_some_and(|module| module.is_standard_library)
    }

    pub fn current_execution_mode(&self) -> TrustedOrRequireVerify {
        self.execution_options.trusted_or_require_verify
    }

    pub fn current_execution_is_trusted_source(&self) -> bool {
        self.current_execution_mode() == TrustedOrRequireVerify::Trusted
    }

    pub(crate) fn mark_source_execution_started(&mut self) {
        self.bootstrap_source_pending = false;
    }

    pub fn record_unverified_import(
        &mut self,
        kind: UnverifiedImportKind,
        name: String,
        line_file: LineFile,
    ) {
        if self
            .module_manager
            .unverified_imports
            .iter()
            .any(|entry| entry.kind == kind && entry.name == name && entry.line_file == line_file)
        {
            return;
        }
        self.module_manager
            .unverified_imports
            .push(UnverifiedImport {
                kind,
                name,
                line_file,
            });
    }

    pub fn unverified_imports(&self) -> &[UnverifiedImport] {
        &self.module_manager.unverified_imports
    }

    pub fn replace_current_execution_mode(
        &mut self,
        execution_mode: TrustedOrRequireVerify,
    ) -> TrustedOrRequireVerify {
        let previous = self.execution_options.trusted_or_require_verify;
        self.execution_options.trusted_or_require_verify = execution_mode;
        previous
    }
}

impl Runtime {
    pub fn validate_name(
        &mut self,
        name: &str,
        _current_line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if let Err(invalid_name_message) = is_valid_litex_name(name) {
            return Err(ParseRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                invalid_name_message,
            ))
            .into());
        }

        Ok(())
    }

    pub fn validate_user_fn_param_names_for_parse(
        &mut self,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for name in names {
            if let Err(e) = is_valid_litex_name(name) {
                return Err(
                    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        e,
                        line_file.clone(),
                    ))
                    .into(),
                );
            }
        }
        Ok(())
    }

    pub fn validate_names_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        names: &Vec<String>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for name in names {
            self.validate_name_and_insert_into_top_parsing_time_name_scope(
                name,
                line_file.clone(),
            )?;
        }
        Ok(())
    }

    /// Validates identifier syntax only; does not record bindings (see `run_in_local_parsing_time_name_scope`).
    pub fn validate_name_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        name: &str,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        self.validate_name(name, line_file)
    }
}

impl Runtime {
    pub fn start_virtual_source(&mut self, kind: VirtualSource) {
        debug_assert!(self.parse_context.is_at_root_scope());
        let source_id = self.start_standalone_source(SourcePath::VirtualSource(kind));
        self.activate_source(
            ModuleId::ROOT,
            source_id,
            TrustedOrRequireVerify::RequireVerification,
        );
    }

    pub fn start_real_file(&mut self, path: &str) {
        self.start_real_file_path(RealFilePath::new(path));
    }

    pub fn start_real_file_path(&mut self, path: RealFilePath) {
        debug_assert!(self.parse_context.is_at_root_scope());
        let source_id = self.start_standalone_source(SourcePath::RealFilePath(path));
        self.activate_source(
            ModuleId::ROOT,
            source_id,
            TrustedOrRequireVerify::RequireVerification,
        );
    }

    /// Start a standalone virtual source with its own root module.
    #[deprecated(note = "use start_virtual_source with a VirtualSource variant")]
    pub fn start_isolated_source(&mut self, legacy_label: &str) {
        self.start_virtual_source(virtual_source_from_legacy_label(legacy_label));
    }

    /// Start a standalone physical file run with its own root module and source.
    #[deprecated(note = "use start_real_file")]
    pub fn start_isolated_file(&mut self, source_path: &str) {
        self.start_real_file(source_path);
    }

    /// Start a repository run with its root module. Registered sources are
    /// activated by the repository execution pipeline as they execute.
    pub fn start_repository_run(
        &mut self,
        repository_root: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        self.start_repository_run_typed(
            RealDirectoryPath::new(repository_root),
            RealFilePath::new(main_file_path),
        )
    }

    pub fn start_repository_run_typed(
        &mut self,
        repository_root: RealDirectoryPath,
        main_file_path: RealFilePath,
    ) -> Result<ModuleId, String> {
        if !self.bootstrap_source_pending {
            return Err(
                "repository root cannot be started after source execution has begun".to_string(),
            );
        }
        let module_id = self
            .module_manager
            .configure_repository_root_module(repository_root, main_file_path.clone())?;
        self.module_manager
            .module_mut(module_id)
            .and_then(|module| module.source_mut(self.current_source_id))
            .expect("repository discovery source should be registered")
            .origin = SourcePath::VirtualSource(VirtualSource::Named(format!(
            "repository-discovery:{}",
            main_file_path
        )));
        self.bootstrap_source_pending = false;
        Ok(module_id)
    }

    /// After a standalone source has been created, point that current source at
    /// a physical file path without creating another source.
    pub fn set_current_user_lit_file_path(&mut self, path: &str) {
        let module_id = self.current_module_id;
        let source_id = self.current_source_id;
        self.module_manager
            .module_mut(module_id)
            .and_then(|module| module.source_mut(source_id))
            .expect("current user source should be registered")
            .origin = SourcePath::RealFilePath(RealFilePath::new(path));
        if module_id == ModuleId::ROOT {
            self.module_manager
                .module_mut(module_id)
                .expect("root module should exist")
                .location = ModuleLocation::SingleFile;
        }
    }

    /// Make the discovered repository's root module the persistent environment for
    /// interactive input. This method does not itself execute the ordered `[export]` plan.
    #[deprecated(note = "use prepare_current_module_for_virtual_source")]
    pub fn prepare_current_repository_for_repl(
        &mut self,
        source_path: &str,
    ) -> Result<(), RuntimeError> {
        self.prepare_current_module_for_virtual_source(virtual_source_from_legacy_label(
            source_path,
        ))
    }

    pub fn prepare_current_module_for_virtual_source(
        &mut self,
        kind: VirtualSource,
    ) -> Result<(), RuntimeError> {
        debug_assert!(
            self.parse_context.is_at_root_scope(),
            "a repository REPL cannot start inside an active parser scope"
        );
        let inherited_environment = self.current_source().environment.clone();
        let module_id = self
            .module_manager
            .module(ModuleId::ROOT)
            .map(|module| module.id)
            .expect("repository root module should exist");
        let source_id = self
            .module_manager
            .create_virtual_source(module_id, kind)
            .expect("repository REPL source should be registered");
        self.module_manager
            .module_mut(module_id)
            .and_then(|module| module.source_mut(source_id))
            .expect("interactive source should be registered")
            .environment = inherited_environment;
        self.activate_source(
            ModuleId::ROOT,
            source_id,
            TrustedOrRequireVerify::RequireVerification,
        );
        Ok(())
    }

    fn start_standalone_source(&mut self, origin: SourcePath) -> SourceId {
        assert!(
            self.bootstrap_source_pending,
            "a standalone source can only be started before source execution"
        );
        let source_id = self.current_source_id;
        let location = match &origin {
            SourcePath::RealFilePath(_) => ModuleLocation::SingleFile,
            SourcePath::VirtualSource(_) => ModuleLocation::Virtual,
        };
        let module = self
            .module_manager
            .module_mut(ModuleId::ROOT)
            .expect("runtime root module should exist");
        {
            let source = module
                .source_mut(source_id)
                .expect("runtime bootstrap source should be registered");
            source.origin = origin;
            source.canonical_name = None;
            source.load_status = SourceLoadStatus::Loaded;
            source.load_mode = TrustedOrRequireVerify::RequireVerification;
        }
        module.module_source_id = Some(source_id);
        module.location = location;
        self.bootstrap_source_pending = false;
        source_id
    }
}

#[cfg(test)]
#[path = "../../tests/unit/runtime/state/test_support.rs"]
mod test_support;
