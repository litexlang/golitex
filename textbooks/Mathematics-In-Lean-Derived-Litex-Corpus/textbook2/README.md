# Alternative Litex presentations for the MIL-derived corpus

This module contains independent alternative formal presentations of material
from the main `textbook/` module. It is a comparison workspace, not a proof
dependency of the setting-first Chapter 2.

The current export is `chap2_struct`, an independent structure-oriented
Chapter 2. Algebraic systems, orders, lattices, and metric spaces are represented
as first-class struct values whose fields are accessed as `group.mul`,
`ring.add`, or `space.dist`.

Run it from the repository root with:

```sh
RUST_MIN_STACK=8388608 target/release/litex -compact -runner -r scripts/mathematics_in_litex/textbook2
```

The main `textbook/litex.config` imports this module as `MILAlternative` for
the later chapters that retain structure-oriented APIs. The setting-first
`textbook/chapter02-basics.lit` neither cites nor imports this file, and both
Chapter 2 presentations also verify as isolated files.
