# How Are Facts Verified?

Try the examples in browser: https://litexlang.com/doc/Tutorial/How_Are_Facts_Verified

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Tutorial/How_Are_Facts_Verified.md

Litex source code stays the same across languages, but CLI output supports
localized JSON keys and explanatory labels with `litex -lang <code> ...`.
See [CLI](https://litexlang.com/doc/cli) for the supported language codes.

## Atomic Fact

1. Check whether the atomic fact is well-defined.

1.1. Check whether the predicate is defined.

For example, you cannot verify `$abc(1)` unless you define `abc` first.

1.2. Check whether the arguments are well-defined.

For example, you cannot verify `1 / 0 = 0` because `1 / 0` is not well-defined.

2. Use builtin rules to verify the atomic fact.

For example, `1 + 1 = 2` is verified by builtin calculation.

Litex provides rich builtin rules for atomic facts. Their implementation lives
in `src/verify/verify_builtin_rules/`. Explicit `std` or project packages can
provide additional named source facts, but those facts are available only after
the top-level module imports the package in `litex.config`.

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

Whenever Litex verifies an atomic fact, the fact is stored for later use. The
same reuse happens inside a `forall`: facts before `=>:` are available when
checking the conclusions after `=>:`.

```litex
abstract_prop p(a)

forall:
    $p(1)
    =>:
        $p(1)
```

4. Use the definition of the predicate.

```litex
prop p(a, b R):
    a < b

$p(1, 2)
```

5. Use `forall` facts.

If a `forall` fact is in the local context, then `$p(1)` can be verified by
instantiating that universal fact with `a = 1`.

```litex
abstract_prop p(a)
abstract_prop q(a, b)
have f fn(a R) R

forall:
    forall a R:
        $p(a)

    forall a, b R:
        $q(f(a + b), b)
    =>:
        $p(1)
        $q(f(1 + 2), 2)
```
