# Runtime state

`Runtime` is the coordinator for one Litex run. It owns the run-wide module
world, monotone IDs, symbol interners, and output configuration, plus scoped
execution and statement-proof stacks that are cleared or popped at their
actual lifecycle boundaries.

```text
Runtime::new(options: RunOptions)
  module_manager = one shared module world
  execution_stack = []
  next_fact_id = 1
start_isolated_source("example.lit")
  push entry execution frame
run source `1 = 1`
  parse and execute statement
  allocate f1
  clear statement-local proof cache and recursion guards
  pop local frames when their scopes end
```

## Ownership boundaries

| Owner | State and concrete example |
| --- | --- |
| `Runtime` | Stored facts receive `f1`, then `f2`; popped local facts do not cause ID reuse. Its single `RunOptions` value owns run-wide `-compact`, `-detail`, `-strict`, language, summary, and isolation configuration. Its `StatementProofStateStack` mirrors temporary environment scopes but is cleared between statements. |
| `ExecutionFrame` | The active module/file, execution mode, and environment. Import permission is not source-frame state: every Litex source rejects `import`, while an interactive terminal may update its separate ephemeral module manifest before source parsing. |
| `ParseContext` | Free binders and temporary struct/tuple views needed before the current statement executes. A source binder such as `a &Pair` can therefore parse later `a.left` syntax within the same recursive statement. |
| `Environment` | Checked definitions, facts, and persistent mathematical caches. A stored `SymbolDefinition` owns its definition-time struct/tuple views, so exact `SymbolId` references keep working across exported files and imported modules. Child-environment merge commits this mathematical state; transient statement-proof cache entries and recursion guards are not part of the merge. |
| `ModuleManager` | Repository/module lifecycle plus parse-only struct definitions and unverified-import diagnostics shared by files in that module world. |
| Local matcher values | Recursive forall-argument bindings live only for the operation using them; they are not ambient `Runtime` state. |

Start with [`runtime.rs`](runtime.rs) for the `Runtime` fields and run initialization,
[`run_options.rs`](run_options.rs) for run configuration, and [`execution_frame.rs`](execution_frame.rs)
for active execution frames. The remaining code is
grouped by the state or operation it owns:

- [`name_resolution/`](name_resolution/) owns local parser scopes, symbol and
  binder policy, parameter definition, object resolution, and internal names.
  Kernel-generated binders use `____binder_<id>`; the tokenizer reserves the
  four-underscore prefix from user-authored symbol tokens.
- [`definition_state/`](definition_state/) owns definition lookup and support,
  known object properties, and parameter-type facts.
- [`instantiation/`](instantiation/) owns capture-avoiding fact, object, and
  function-forall instantiation.
- [`statement_proof_state.rs`](statement_proof_state.rs) owns statement-local
  proof reuse and recursion guards; [`fact_storage.rs`](fact_storage.rs) owns
  FactId-backed storage and its immediate closure inference.

The two proof lookup layers have deliberately different names:
`verification_result_from_statement_proof_cache` reads transient proof reuse
for the current statement, while `verification_result_from_known_fact_cache`
reads persistent facts owned by `Environment`. Successful transient proofs are
inserted by `cache_successful_atomic_fact_for_statement`.

Then follow [`execution_frame.rs`](execution_frame.rs) for source scopes,
[`parse_context.rs`](parse_context.rs) for parser metadata, and
[`../environment.rs`](../environment.rs)
for checked definitions, stored facts, and persistent mathematical caches.
