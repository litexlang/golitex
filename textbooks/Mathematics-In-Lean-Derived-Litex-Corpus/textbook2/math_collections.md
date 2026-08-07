# Alternative-presentation interface map

This module collects mathematically equivalent Litex presentations whose
representation choices differ from the default corpus. Each presentation must
state and prove its own mathematical laws; alternative files are comparison
artifacts, not proof wrappers around the default implementation.

## Structure-first Chapter 2

`chapter02-basics-struct.lit`, exported as `chap2_struct`, represents an
algebraic or ordered system as a first-class value. Its principal interfaces
include:

```litex
struct AdditiveCommutativeGroup<s nonempty_set>:
    add fn(x, y s) s
    zero s
    neg fn(x s) s

struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s

struct Ring<s nonempty_set>:
    add fn(x, y s) s
    zero s
    neg fn(x s) s
    mul fn(x, y s) s
    one s
```

This form is appropriate when a mathematical statement constructs, compares,
or transports whole systems. Its theorem proofs are local to this module. The
setting-first presentation in `../textbook/chapter02-basics.lit` independently
uses direct operations and setting laws instead.

The nearest rejected architecture is a comparison file that proves one
presentation by citing the other. Such a dependency would measure wrapper
syntax rather than two genuine formalization choices.
