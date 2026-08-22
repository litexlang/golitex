# Runtime state

One `litex -runner -e '1 = 1'` run owns one module world, one execution-frame stack, one monotone FactId allocator, and one set of recursion guards.

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

## Examples and boundaries

| Runtime state | Concrete example |
| --- | --- |
| Execution frame | Parsing `forall x R:` followed by indented `x = x` tracks `x` in the current frame. |
| Shared module manager | An imported module and its parent update the same cycle/status table. |
| FactId allocator | Stored facts receive `f1`, then `f2`; popped local facts do not cause ID reuse. |
| Recursion guard | Re-entering the same well-definedness object stops an infinite cycle. |
| Output mode | `-compact`, normal, and `-detail` select different render detail from the same result. |
| Strict mode | `-strict -e 'trust 1 = 2'` rejects the trusted statement. |

Start with [`runtime.rs`](runtime.rs) for run-wide state and [`execution_frame.rs`](execution_frame.rs) for examples such as module, file, and local proof scopes.
