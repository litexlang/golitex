# Runtime state

`Runtime` is the coordinator for one Litex run. It owns the run-wide module
world, monotone IDs, symbol interners, and output configuration, plus scoped
execution frames. Recursive proof-search state is carried explicitly by
`VerifyState`, not stored on `Runtime`.

```text
Runtime::new(options: RunOptions)
  module_manager = one shared module world
  execution_stack = []
  next_fact_id = 1
start_isolated_source("example.lit")
  register ModuleId::ROOT/FileId(0)
  push the registered file's execution frame
run source `1 = 1`
  parse and execute statement
  allocate f1
  pop local frames when their scopes end
```

## Ownership boundaries

| Owner | State and concrete example |
| --- | --- |
| `Runtime` | Stored facts receive `f1`, then `f2`; popped local facts do not cause ID reuse. It also retains execution-derived direct struct carriers by exact `SymbolId`, so a stored theorem can later instantiate field syntax whose original binder scope has ended. Its single `RunOptions` value owns run-wide output style, strictness, language, summary, and isolation configuration for internal and embedding callers; the CLI fixes its output style and summary behavior. |
| `VerifyState` | Owns one explicit proof-search tree: successful atomic/WD memos and recursion guards. A child proof scope can read parent memos, while child entries never become visible in its parent. It also carries the explicit `InferenceState` used by stores reached from that verification tree. A fresh top-level state starts a fresh search. |
| `ExecutionFrame` | The active registered module/file plus transient execution mode, parser state, and local scopes. Its `ExecutionModuleFileInfo` contains `ModuleId`, module-local `FileId`, and the source label/path. Import permission is not source-frame state: every Litex source rejects `import`, while an interactive terminal may update its separate ephemeral module manifest before source parsing. |
| `ParseContext` | Free binders and scoped parse bindings needed to construct symbol-aware syntax trees. Field syntax is stored only as receiver plus field name; the parser does not choose a struct carrier. |
| `Environment` | Checked definitions, facts, and persistent mathematical caches. A stored `SymbolDefinition` may own the direct struct carrier declared for that exact `SymbolId`; execution and well-definedness resolve field access from it. Tuple carriers are not retained as parser or symbol metadata. Child-environment merge commits this mathematical state; proof-search memos and recursion guards are not environment data. |
| `ModuleManager` | Repository/module/file lifecycle and every persistent file environment, plus parse-only struct definitions and unverified-import diagnostics shared by files in that module world. `ModuleId::ROOT` is always zero. |
| Local matcher values | Recursive forall-argument bindings live only for the operation using them; they are not ambient `Runtime` state. |

Start with [`runtime.rs`](runtime.rs) for the `Runtime` fields and run initialization,
[`run_options.rs`](run_options.rs) for run configuration,
[`execution_module_file_info.rs`](execution_module_file_info.rs) for registered source identity,
and [`execution_frame.rs`](execution_frame.rs) for transient execution state. The remaining code is
grouped by the state or operation it owns:

- [`name_resolution/`](name_resolution/) owns local parser scopes, symbol and
  binder policy, parameter definition, object resolution, and internal names.
  Kernel-generated binders use `____binder_<id>`; the tokenizer reserves every
  double-underscore prefix from user-authored symbol tokens.
- [`definition_state/`](definition_state/) owns definition lookup and support,
  direct struct-carrier resolution, known object properties, and parameter-type facts.
- [`instantiation/`](instantiation/) owns capture-avoiding fact, object, and
  function-forall instantiation.
- [`../verification/proof_search/state.rs`](../verification/proof_search/state.rs)
  owns the scope tree for transient proof reuse and recursion guards;
  [`../verification/proof_search/memo.rs`](../verification/proof_search/memo.rs)
  connects those memos to atomic verification.
  [`../verification/well_definedness/local_environment.rs`](../verification/well_definedness/local_environment.rs)
  couples every verifier-local `Environment` with one child proof scope, so
  both lifetimes end at the same Rust function boundary.
  [`fact_storage.rs`](fact_storage.rs) owns FactId-backed storage and its
  immediate closure inference, while
  [`../inference/state.rs`](../inference/state.rs) owns the transient inference
  recursion guard.

The two proof lookup layers have deliberately different names:
`verification_result_from_proof_search_memo` reads transient reuse from the
explicit `VerifyState`, while `verification_result_from_known_fact_cache`
reads persistent facts owned by `Environment`. Successful transient proofs are
inserted by `remember_successful_atomic_fact_for_proof_search`.

Then follow [`execution_frame.rs`](execution_frame.rs) for source scopes,
[`parse_context.rs`](parse_context.rs) for parser metadata, and
[`../environment/environment.rs`](../environment/environment.rs)
for checked definitions, stored facts, and persistent mathematical caches.
