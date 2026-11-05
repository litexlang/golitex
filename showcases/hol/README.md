# A shallow HOL interpretation

This showcase presents the existing development provided by **chegnxuan huang**:
Boolean truth values lead to higher-order reasoning and constructed arithmetic.
Read [main.lit](main.lit) in that order. Its mathematical source is preserved
from [the standalone example](../../examples/hol_embedding.lit); only the
module/run comments change. The original example remains untouched.
The local caller's `validation/litex.config` imports this showcase with:

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

The mathematical source still contains the original demonstration facts,
including two-plus-two. Importing the showcase checks that whole development;
this first extraction does not claim a minimal-load split of its logic and
arithmetic layers.

```bash
target/release/litex -strict -lang en -f showcases/hol/main.lit
target/release/litex -strict -lang en -f showcases/hol/validation/main.lit
```

Focused results and hashes are in [acceptance.json](validation/acceptance.json).
[negative_cases.json](validation/negative_cases.json) checks false truth,
arithmetic and beta conclusions after the independent positive caller.

The source has no user axiom or trust statement. It uses Litex's native
set/function theory, N and fixed Axiom of Choice foundation. This is a shallow
interpretation: it does not implement HOL Light's full object syntax, proof
calculus, certificate import, or an independent consistency proof. No Lean
replay is claimed.
