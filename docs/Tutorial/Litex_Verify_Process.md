# Litex verify process

Online doc: https://litexlang.com/doc/Tutorial/Litex_Verify_Process
Github: https://github.com/litexlang/golitex/blob/main/docs/Tutorial/Litex_Verify_Process.md


# Atomic Fact

1. check whether the atomic fact is well-defined:

1.1 check whether the predicate is defined

e.g. You can't verify `$abc(1)` unless you define `abc` first.

1.2 check whether the arguments are well-defined

e.g. You can't verify `1/0 = 0` because `1/0` is not well-defined.

2. Use builtin rules to verify the atomic fact:

e.g. `1 + 1 = 2` is verified by builtin rule calculation.

Litex provides you with rich builtin rules to verify the atomic fact. You can find the builtin rules in the `src/builtin_code/` and `src/verify/verify_builtin_rules/`.

```litex
1 + 1 = 2
1 < 2

# builtin rule for polynomial expansion
forall a, b R:
    (a + b)^ 2 = a^2 + 2 * b * a + b * b

# builtin rule for inequality
forall a, b R:
    a < b
    =>:
        0 < b - a
```

3. Use known atomic facts to verify the atomic fact:

Anytime you verify an atomic fact, the fact is stored in the environment for future use. For example, you may verify `$p(1, 2)` on line 4 and on line 10 you write `$p(1, 2)`, then the fact `$p(1, 2)` is verified by the fact known on line 4.

```litex
abstract_prop p(a)

know $p(1)

$p(1)
```

4. Use definition of the predicate to verify the atomic fact:

```litex
prop p(a, b R):
    a < b

$p(1, 2)
```

5. Use forall facts to verify the atomic fact:

For example, you may have verified `forall a R: $p(a)` on line 4 and on line 10 you write `$p(1)`, then the fact `$p(1)` is verified by the fact known on line 4 by replacing `a` with `1`.

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