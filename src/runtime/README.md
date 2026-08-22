# Runtime state

`Runtime` is the coordinator for one Litex run. It owns only state whose
lifetime really spans that run: the module world, execution-frame stack,
monotone IDs and symbol interners, plus output/strictness configuration.

```text
Runtime::new()
  module_manager = one shared module world
  execution_stack = []
  next_fact_id = 1
run source `1 = 1`
  push entry execution frame
  parse and execute statement
  allocate f1
  pop local frames when their scopes end
```

## Ownership boundaries

| Owner | State and concrete example |
| --- | --- |
| `Runtime` | Stored facts receive `f1`, then `f2`; popped local facts do not cause ID reuse. `-compact`, `-detail`, and `-strict` are run-wide configuration. |
| `ExecutionFrame` | The active module/file and whether that source permits inline imports. Repository files default to no inline imports; isolated source and REPL frames opt in. |
| `ParseContext` | Free binders and parser-only struct/tuple views. A source binder such as `a &Pair` records how later `a.left` syntax lowers, without changing the verified environment. |
| `Environment` | Checked declarations/facts/caches and statement-local `ProofSearchState`. Re-entering the same well-definedness object is suppressed in the visible environment chain; clone and child merge do not persist an in-progress search. |
| `ModuleManager` | Repository/module lifecycle plus parse-only struct declarations and unverified-import diagnostics shared by files in that module world. |
| Local matcher/runner values | Recursive forall-argument bindings and trusted-prefix policy/report live only for the operation using them; they are not ambient `Runtime` state. |

Start with [`runtime.rs`](runtime.rs) for run-wide state,
[`execution_frame.rs`](execution_frame.rs) for source scopes,
[`parse_context.rs`](parse_context.rs) for parser metadata, and
[`../environment/environment.rs`](../environment/environment.rs) for checked
and statement-local proof state.
