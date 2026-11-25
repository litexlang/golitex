<div align="center">
  <img src="./assets/logo.PNG" alt="Litex logo" width="300">

# Litex

### A High-Level Language for Formal Mathematics

[Website & Playground](https://litexlang.com/) · [Manual](docs/Manual.md) · [Setup](docs/setup.md) · [中文说明](docs/中文README.md)
</div>

Litex lets you write mathematical objects, definitions, statements and proofs
close to ordinary mathematical writing. Its native checker checks domains and
proof steps, and makes accepted facts available to later statements.

```litex
have a R = 2
a + 1 = 3
```

The first line introduces a real number and its value. The second states a fact
that the checker verifies using that context. A persistent Session lets you
continue from accepted statements while correcting a failed step.

## Install and run

On macOS or Linux:

```bash
brew install litexlang/tap/litex
```

On Windows:

```powershell
scoop bucket add litex https://github.com/litexlang/scoop-litex
scoop install litex
```

For other installation options, see the [setup guide](docs/setup.md).

```bash
# Check a fact
litex -e '1 + 1 = 2'

# Start an interactive Session
litex -session

# Check a saved proof
litex -f proof.lit
```

## Documentation

| Task | Reference |
| --- | --- |
| Learn the language | [Tutorial](docs/Learn_Litex.md), [cheatsheet](docs/Litex_Learner_Cheatsheet.md) |
| Look up syntax, domains and proof rules | [Manual](docs/Manual.md) |
| Use the command line and read JSON output | [CLI reference](docs/cli.md) |
| Write proofs with an agent | [Agent Guide](docs/AgentGuide.md), [primer](docs/Litex_Agent_Primer.md) |
| Compile supported proofs to Lean | [Compiler guide](docs/Litex_To_Lean_Compiler_Guide.md) |
| Read mathematical examples | [Examples](examples/README.md), [sample chapters](docs/mathematical_sample_chapters/README.md), [showcases](showcases/README.md) |

<a id="litex-reliability"></a>

## Status and scope

Litex is under active development. The Lean backend compiles supported proof
routes for independent checking; coverage and limitations are described in the
[compiler guide](docs/Litex_To_Lean_Compiler_Guide.md). The manual describes the native checker's
[trust boundary](docs/Manual.md#trust-boundary).

Created and maintained by Jiachen Shen. Report bugs with a minimal example at
[GitHub Issues](https://github.com/litexlang/golitex/issues). Community discussion
is on [Zulip](https://litex.zulipchat.com/).

Released under the [Apache License 2.0](LICENSE).
