# Mathematical environment

After Litex checks `have a R = 1`, the environment stores the symbol `a`, its value/equality information, and indexes that later let `a + 1 = 2` reuse it.

```text
store checked fact `a = 1`
  allocate FactId, for example f3
  add equality edge a <-> 1
  update known object value for a
  index atomic/forall/set/function facts by their shapes
  run inference and cache derived checked facts
later goal `a + 1 = 2`
  resolve a through the stored equality/value
```

## Examples and boundaries

| Stored item | Later use |
| --- | --- |
| `a = 1` | Resolves `a + 1 = 2`. |
| `a $in A` and `A $subset B` | Supports deriving or verifying `a $in B`. |
| `forall x R:`<br>&nbsp;&nbsp;`x = x` | Is indexed by fact and argument shape for later instantiation. |
| A fact inside a failed `try:` | Is discarded with that temporary environment. |
| A cached proof from a popped local scope | Cannot be retargeted to a different ambient fact merely because the text matches. |

Start with [`environment.rs`](environment.rs) for the stored world and [`known_equality.rs`](known_equality.rs) for examples such as `a = 1 = b`.
