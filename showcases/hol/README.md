# A shallow HOL interpretation

This showcase develops higher-order reasoning and constructed arithmetic from
Boolean truth values. Start with [the original standalone example](../../examples/hol_embedding.lit)
provided by **chegnxuan huang**, or run [v3](main.lit), the importable
version used by this module.

The local caller imports v3 through `validation/litex.config`.

```ini
[import]
HOL = ".."
[alias]
hol = HOL::main
[export]
main = "./main.lit"
```

Predicates are actual functions into `Bool`; `holds` connects Boolean values
to Litex assertions. The showcase supplies Boolean connectives, equality,
universal/existential quantifiers, introduction/elimination rules, beta/eta
and function extensionality. It interprets HOL Light's eta, choice and infinity
axioms, then constructs `HolNat`, induction, numeral conversion and addition.

The [independent caller](validation/main.lit) checks a generic beta law,
quantification over all predicates on N and arithmetic on constructed
naturals. Imported callable definitions must be released where used: in
particular the caller releases `plus` before consuming its arithmetic
conclusions and `hol_of_nat` before numeral-conversion conclusions. Boolean
and natural carrier/constants are released explicitly too.

## Organizing checked examples

Keep shared definitions and theorems in the module scope. Put intermediate
facts inside the proof that needs them. For example,
`hol_nat_induction_body_eval` establishes `\hol_all<HolNat>(q) $in Bool`
before checking the enclosing implication. The numeral index's successor
law uses `release obj def hol_to_nat` to retrieve the function specification.

Follow the proof dependencies when classifying a concrete calculation.
The equations for converting 2, 3, and 4 are consumed by the two arithmetic
theorems. They are collected in `hol_small_numeral_conversions` and explicitly
released inside those proofs.

Put independent demonstrations in small `sketch` blocks. Each block is checked
and its scope is discarded afterward. For example, the Boolean demonstrations
include these instances.

```litex
sketch:
    release thm hol_not_intro(False)
    release thm hol_and_intro(True, True)
    release thm hol_or_intro_right(False, True)
```

The six sketches follow the main construction. Importing the showcase still
checks them. An independent demo caller can be used when consumers only
need to load the definitions and theorems.

```bash
target/release/litex -strict -lang en -f examples/hol_embedding.lit
target/release/litex -strict -lang en -f showcases/hol/main.lit
target/release/litex -strict -lang en -f showcases/hol/validation/main.lit
```

The [acceptance check](validation/acceptance.json) records the strict runs,
the local sketch steps, and the independent caller. The [negative cases](validation/negative_cases.json)
test false Boolean, arithmetic, and beta conclusions. The acceptance check also records the qualified lookup of the theorem local
to the reflexivity sketch, which is rejected.

The source uses Litex's native set and function theory, N, and its fixed
Axiom of Choice. Strict mode checks the development without user axioms or
trust statements. The scope is the shallow interpretation of HOL expressions
and the three interpreted axioms.
