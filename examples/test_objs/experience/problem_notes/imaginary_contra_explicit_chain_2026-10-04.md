# Imaginary-unit contradiction: explicit square substitution

Date: 2026-10-04. Status: checkable authoring solution.

The user explicitly chose to retain the existing natural substitution mechanism and repair the Litex proof, with no Rust change. Assuming `i=0`, expose both factor substitutions in one equality chain. Preserve the original mathematical target and contradiction tail:

```lit
by contra:
    ? i != 0
    i * i = -1
    i * i = 0 * 0 = 0
    impossible i * i != 0
```

The old squared-i proof omitted the `i*i = 0*0 = 0` bridge; its automatic rewrite route could choose `i*i -> -1` before `i -> 0`. Historical diagnosis and raw evidence are retained in [the causal note](../../contra_rewrite_order_2026-10-04.md). That automatic shortcut was not changed; it is not a pending Rust request for this example.

Canonical acceptance: [Stmt example](../../../stmt_nodes/by/by_contra_imaginary_unit.lit) and [Obj P103](../../imaginary_unit.lit). P103 is registered in the Obj fixture manifest. The original eight imaginary-unit positive cases remain present.

Evidence: accepted in one strict current-CLI session using discarded sketches, with a failed `i=0` control followed by another accepted candidate; both clean files pass; the exact unwrapped proof passes 30/30 serial independent processes; all three existing imaginary-unit negative fixtures reject; the equality chain outside its reverse assumption also rejects. Inventory audit passes for all 99 Obj leaves/files, and the targeted owning file executes all nine cases. No trust, new helper, theorem wrapper, Rust change, or verifier permission change.

Liveness: `i*i=0*0=0` is the explicit mathematical substitution selected by the user and supplies the closing equality path. `i*i=-1` is the intrinsic square identity exposing the other side of the contradiction. No repeated final goal or equality waterfall was added.

Current release source: `a06c85ab99cdc8c93bdd5ca16ffbef45cd0a84f821332c026ebba724590bd34a`; binary: `63d9eae79691e05a13c3f41ffb3b82b5844199fd149d2a4b42189b085df5175a`. Rust source remains identical before build, after build/archive, and after the focused gates. Broader Rust/whole-corpus gates were skipped because this is an authoring-only update.

[Journal](../../proof_journals/imaginary_contra_explicit_chain_2026-10-04.json) · [Receipt](../../proof_journals/imaginary_contra_explicit_chain_2026-10-04_receipts.zip) (SHA-256 `baff7d92ecca895da507bace408fa2667ece5cd57964efff7643669356d7cd55`). Exact accepted fixture sources, old sources, all clean gate output, source archive and verified executable are preserved.
