# Runtime state

`Runtime` is the coordinator for one Litex run. It owns the run-wide module
world, monotone IDs, symbol interners, and output configuration, plus scoped
execution and statement-proof stacks that are cleared or popped at their
actual lifecycle boundaries.

```text
Runtime::new()
  module_manager = one shared module world
  execution_stack = []
  next_fact_id = 1
start_isolated_source("example.lit")
  push entry execution frame
run source `1 = 1`
  parse and execute statement
  allocate f1
  clear statement-local proof memo and recursion guards
  pop local frames when their scopes end
```

## Ownership boundaries

| Owner | State and concrete example |
| --- | --- |
| `Runtime` | Stored facts receive `f1`, then `f2`; popped local facts do not cause ID reuse. `-compact`, `-detail`, and `-strict` are run-wide configuration. Its `StatementProofStateStack` mirrors temporary environment scopes but is cleared between statements. |
| `ExecutionFrame` | The active module/file and whether that source permits inline imports. Repository files default to no inline imports; isolated source and REPL frames opt in. |
| `ParseContext` | Free binders and temporary struct/tuple views needed before the current statement executes. A source binder such as `a &Pair` can therefore parse later `a.left` syntax within the same recursive statement. |
| `Environment` | Checked declarations, facts, and persistent mathematical caches. A stored `SymbolDefinition` owns its declaration-time struct/tuple views, so exact `SymbolId` references keep working across exported files and imported modules. Child-environment merge commits this mathematical state; transient proof memo entries and recursion guards are not part of the merge. |
| `ModuleManager` | Repository/module lifecycle plus parse-only struct declarations and unverified-import diagnostics shared by files in that module world. |
| Local matcher/runner values | Recursive forall-argument bindings and trusted-prefix policy/report live only for the operation using them; they are not ambient `Runtime` state. |

Start with [`runtime_state.rs`](runtime_state.rs) for the `Runtime` fields,
run initialization, output configuration, and active execution frames;
[`runtime_local_scopes.rs`](runtime_local_scopes.rs) for temporary environment
and parser scopes; and
[`runtime_definition_support.rs`](runtime_definition_support.rs) for definition
name checks, known-object metadata, callable construction, and parameter maps.
Then follow [`execution_frame.rs`](execution_frame.rs) for source scopes,
[`parse_context.rs`](parse_context.rs) for parser metadata, and
[`../environment/environment_state.rs`](../environment/environment_state.rs)
for checked declarations, stored facts, and persistent mathematical caches.
