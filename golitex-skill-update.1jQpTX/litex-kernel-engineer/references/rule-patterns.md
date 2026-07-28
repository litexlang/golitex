# Rule Patterns

## Builtin Rule Checklist

A builtin rule should have:

- a narrow mathematical property;
- explicit applicability conditions;
- predictable failure behavior;
- a runnable example;
- a regression test or covered example;
- verifier output that names the rule clearly enough for debugging.

Example comment shape:

```rust
// Proves nonzero quotients from nonzero numerator and denominator.
// Example: a != 0, b != 0 => a / b != 0.
```

## Infer Rule Checklist

An infer rule should say:

- when it is applied;
- what fact it adds;
- why the inference is mathematically safe;
- an example of the source fact and inferred fact.

Prefer a narrowly targeted inference over a broad one that changes many unrelated proofs.
