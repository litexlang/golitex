# Runtime state

`Runtime` is the coordinator for one Litex run. It owns the run-wide module
world, monotone IDs, symbol interners, output configuration, one transient
parser context, and the currently active source. Recursive proof-search state
is carried explicitly by `VerifyState`, not stored on `Runtime`.

```text
Runtime::new(options: LitexExecutionOptions)
  module_manager = one shared module world with a registered Eval source
  current_module_id = ModuleId::ROOT
  current_source_id = SourceId(0)
  next_fact_id = 1
start_real_file("example.lit")
  reuse the constructor source as ModuleId::ROOT/SourceId(0)
  update its origin and keep the current source pair
run source `1 = 1`
  parse and execute statement
  allocate f1
  local scopes are owned by Runtime and are cleared at source boundaries
```

## Ownership boundaries

| Owner | State and concrete example |
| --- | --- |
| `Runtime` | Stored facts receive `f1`, then `f2`; popped local facts do not cause ID reuse. It owns the one transient `ParseContext` shared across recursive parsing of a compound statement. It also retains execution-derived direct struct carriers by exact `SymbolId`, so a stored theorem can later instantiate field syntax whose original binder scope has ended. Its `LitexExecutionOptions` value owns verification strictness, output detail, language, and summary settings; source selection and isolation remain with the command or pipeline entry point. |
| `VerifyState` | Owns one explicit proof-search tree: successful atomic/WD memos and recursion guards. A child proof scope can read parent memos, while child entries never become visible in its parent. It also carries the explicit `InferenceState` used by stores reached from that verification tree. A fresh top-level state starts a fresh search. |
| `current source` | `Runtime.current_module_id` plus `Runtime.current_source_id` always identifies one registered `Source`; the pair is concrete for the lifetime of Runtime. `Runtime.is_current_file_trusted` and `Runtime.execution_environments_stack` hold only active invocation state. `SourcePath::RealFilePath` is the only source origin accepted by filesystem/module path logic; `SourcePath::VirtualSource` is used for eval, REPL, session, generated projections, and `VirtualSource::Named` embedding labels. |
| `SourceActivation` | A short-lived checkpoint used by graph/rendering helpers while they temporarily activate another registered source. It is not a second source registry or a persistent source stack. |
| `ParseContext` | Runtime-owned free binders and scoped parse bindings needed to construct symbol-aware syntax trees before nested statements execute. It must return to its root scope before the current source changes. Field syntax is stored only as receiver plus field name; the parser does not choose a struct carrier. |
| `Environment` | Checked definitions, facts, persistent mathematical caches, and the object-to-`WellDefinednessId2` index. A stored `SymbolDefinition` may own the direct struct carrier declared for that exact `SymbolId`; execution and well-definedness resolve field access from it. Tuple carriers are not retained as parser or symbol metadata. Child-environment merge commits this mathematical state; proof-search memos and recursion guards are not environment data. |
| `ModuleManager` | Repository/module/file lifecycle and every persistent file environment, plus unverified-import diagnostics shared by files in that module world. `ModuleId::ROOT` is always zero. |
| Local matcher values | Recursive forall-argument bindings live only for the operation using them; they are not ambient `Runtime` state. |

The acceptance boundary is exercised by
`structured_source_run_uses_the_constructor_source_context` and
`runtime_constructor_registers_an_active_eval_source`. The former behavior
returned an error when `execute_source` was called before a source was selected;
the current behavior executes through the constructor-registered
`ModuleId::ROOT`/`SourceId(0)` source. Repository setup is covered by
`repository_start_reuses_the_registered_constructor_source`, which keeps that
same concrete pair active while discovery configures the root module.

Start with [`runtime.rs`](runtime.rs) for the `Runtime` fields and run initialization,
[`execution_options.rs`](execution_options.rs) for Litex execution configuration,
[`../module_system/module_records.rs`](../module_system/module_records.rs) for typed source identity. The remaining code is
grouped by the state or operation it owns:

- [`name_resolution/`](name_resolution/) owns local parser scopes, symbol and
  binder policy, parameter definition, object resolution, and internal names.
  Kernel-generated binders use `____binder_<id>`; name validation reserves every
  double-underscore prefix from user-defined names.
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

Then follow [`parse_context.rs`](parse_context.rs) for parser metadata, and
[`../environment/environment.rs`](../environment/environment.rs)
for checked definitions, stored facts, and persistent mathematical caches.
