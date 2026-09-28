# Compatibility module paths

This directory keeps one-version Rust module aliases after source owners move.
For example, `litex::common::fact_id::FactId` re-exports the canonical
`litex::fact::id::FactId`; it does not contain a second fact-ID implementation.

New code should import from the responsibility owner. Compatibility modules are
pure wiring and may be removed after the announced migration window.
