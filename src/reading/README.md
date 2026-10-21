# Interactive textbook reading

This module is the home for turning Litex source and its verification evidence
into an interactive textbook. A reader should be able to select a statement,
inspect the grounds actually used to establish it, and follow those grounds
back to facts, definitions and rules. Concept highlighting follows resolved
symbol identity, separately from proof dependencies.

## Current status

Only the Rust module declaration and this design documentation exist.
There is no reading exporter, public reading schema, browser viewer, HTTP
service, static export command or `-reading` CLI mode yet.

[DESIGN.md](DESIGN.md) records the proposed responsibilities, command shapes,
website integration, implementation sequence and acceptance criteria. It is
a design proposal, not a statement of implemented support or a frozen API.

## Ownership

The reading subsystem will own the exported reading model, its projection
from checked results, source/occurrence mappings, rule catalogue export,
and the reusable browser viewer and its assets. Local preview and published
websites should consume the same model and viewer.

Existing components retain their responsibilities:

- [run](../run/README.md) and [run_module](../run_module/README.md) load and
  execute sources in their real project context.
- [execute](../execute/README.md) and
  [store_fact_and_infer](../store_fact_and_infer/README.md) produce typed
  verification, storage and inference evidence.
- [json_output](../json_output/README.md) retains its current Normal, Compact
  and Detailed contracts. Reading will be a separate projection of the typed
  evidence, without decoding localized JSON or replacing the evidence owners.
- [identifier_identity.md](../identifier_identity.md) defines symbol identity;
  [TokenBlock](../tokenize/token_block.rs) retains original token byte ranges.

Future CLI dispatch belongs in the existing launch/run layers and should
delegate reading work here. Reading must preserve statement transactions,
scope visibility, source order and explicit trust boundaries.
