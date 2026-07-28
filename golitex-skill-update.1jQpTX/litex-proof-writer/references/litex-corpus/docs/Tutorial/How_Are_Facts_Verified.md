# How Are Facts Verified?

Try all snippets in browser: https://litexlang.com/doc/Tutorial/How_Are_Facts_Verified

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Tutorial/How_Are_Facts_Verified.md

## Atomic Fact

1. Check whether the atomic fact is well-defined.

1.1. Check whether the predicate is defined.

For example, you cannot verify `$abc(1)` unless you define `abc` first.

1.2. Check whether the arguments are well-defined.

For example, you cannot verify `1 / 0 = 0` because `1 / 0` is not well-defined.

2. Use builtin rules to verify the atomic fact.

For example, `1 + 1 = 2` is verified by builtin calculation.

Litex provides rich builtin rules for atomic facts. The implementation lives
mostly in `src/builtin_code/` and `src/verify/verify_builtin_rules/`.

```litex
1 + 1 = 2
1 < 2

# builtin rule for polynomial expansion
forall a, b R:
    (a + b)^2 = a^2 + 2 * b * a + b * b

# builtin rule for inequality
forall a, b R:
    a < b
    =>:
        0 < b - a
```

3. Use known atomic facts.

Whenever Litex verifies an atomic fact, the fact is stored in the environment
for future use. For example, if `$p(1)` is known on one line, a later `$p(1)`
can be verified by reusing that known fact.

```litex
abstract_prop p(a)

know $p(1)

$p(1)
```

4. Use the definition of the predicate.

```litex
prop p(a, b R):
    a < b

$p(1, 2)
```

5. Use `forall` facts.

If Litex has already verified `forall a R: $p(a)`, then a later `$p(1)` can be
verified by instantiating the universal fact with `a = 1`.

```litex
abstract_prop p(a)
abstract_prop q(a, b)
have f fn(a R) R

know forall a R:
    $p(a)

know forall a, b R:
    $q(f(a + b), b)

$p(1)
$q(f(1 + 2), 2)
```
