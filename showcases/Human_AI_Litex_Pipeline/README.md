# From Group Axioms to Sylow Theorem: Inside Litex's AI Proof Pipeline

Created and maintained by Jiachen Shen

> Reliable AI mathematics does not require trusting one enormous answer. It
> requires a process in which every accepted fact becomes checked context and
> every failed proposal becomes local repair evidence.

## Why this showcase exists

Many AI proof demonstrations are organized around the final question: did the
model produce a proof? This repository focuses on a different question: how
can a human and an AI build mathematical knowledge together without confusing
proposal with verification or losing useful evidence when a proposal fails?

The distinctive Litex idea shown here is **transactional, fact-oriented
collaboration**. The human fixes the mathematical intent and boundaries; the
AI proposes the next small fact; Litex either commits that fact to the checked
context or rolls it back without contaminating earlier progress; structured
JSON records enough evidence to repair the local failure. The unit of progress
is therefore not “the AI says the proof is complete,” but “the verifier has
accepted the next reusable piece of mathematics.”

The running example is the first Sylow existence theorem because it is too deep
to make a one-shot story credible. The development must grow from groups to
homomorphisms, subgroups, actions, Cauchy's theorem, normalizers, quotient
preimages, and finally the prime-power subgroup. Its short final theorem is the
endpoint of an inspectable dependency graph, not a substitute for that graph.

This showcase demonstrates the collaboration architecture; it does not claim
that the AI autonomously chose the mathematics or that the legacy source
currently passes an unchanged verifier. It is an artifact-first snapshot:
canonical sources remain at the root, accepted fragments are under
[`accepted/`](accepted/), checkpoints under [`checkpoints/`](checkpoints/),
replay copies under [`replay/`](replay/), and run journals under
[`proof_journals/`](proof_journals/). The current `litex.config` and `.order`
make the module and reading order explicit; the former browser UI is not
included. Historical command strings inside the JSON journals retain their
creation-time paths, including `web/`, so the recorded evidence is not
rewritten after the fact.

## First principles, made concrete

The general Litex + AI loop is described in [`SKILL.md`](SKILL.md). This development makes its central principles visible as repository artifacts rather than leaving them as abstract advice:

| First principle | How the Sylow development realizes it |
|---|---|
| **Build the mathematical world before proving the final theorem.** Decompose a deep target into concepts and results with an explicit dependency order. | The development does not begin in `sylow.lit`. It begins with [`group.lit`](group.lit), then gives homomorphisms, subgroups, cosets, Lagrange, actions, normality, quotients, prime arithmetic, Cauchy, normalizers, and quotient preimages their own files. [`sylow.lit`](sylow.lit) is the endpoint of the recorded mathematical order; the evidence directories are not premises of the theorem. |
| **Keep mathematical intent, AI proposals, verifier decisions, process memory, and final source distinct.** | The intended endpoint is the first Sylow existence theorem. The AI's candidates and diagnoses live in JSON journals such as [`proof_journals/sylow_journal.json`](proof_journals/sylow_journal.json); Litex records whether each `try:` committed or rolled back; the accepted mathematics lives in the root `.lit` files. None of those roles substitutes for another. |
| **Advance through small, reversible transactions.** A failed local experiment must not destroy the accepted prefix. | In [`proof_journals/proof_journal.json`](proof_journals/proof_journal.json), the subgroup-intersection theorem is tried, deletion-probed, rolled back at progressively narrower goals, and then accepted with only the live closure facts. In [`proof_journals/quotient_preimage_bijection_journal.json`](proof_journals/quotient_preimage_bijection_journal.json), the difficult coordinate bijection is repaired one failed phase at a time instead of rewriting the Sylow argument. |
| **Preserve repair evidence without turning the mathematical source into a debugging transcript.** | Each journal keeps the candidate, verifier evidence, diagnosis, and next change. Once a block commits, only `accepted_litex` is materialized into files such as [`quotient_preimage_bijection.lit`](quotient_preimage_bijection.lit); the failed attempts remain inspectable in JSON. |
| **Verification must be replayable from a clean, ordered state.** Session success alone is not the final claim. | The JSON journals retain the creation-time clean replay evidence and the [`replay/`](replay/) directory retains the corresponding Litex sources. The current `litex.config` exposes the same root source order, but its presence is not a current-HEAD pass. |
| **A verified proof should still be audited for mathematical shape and trust.** | The journals include deletion and liveness probes, the final sources are scanned for `trust` and `abstract_prop`, and the scope note distinguishes the first Sylow theorem proved here from the second and third Sylow theorems. |

## AI in the loop means fixed roles

“Using AI” is meaningful here only because no participant silently takes over another participant's authority:

- **The human owns mathematical intent:** the target, definitions, assumptions, semantic boundaries, and final judgment about whether the result still says the intended mathematics.
- **The AI owns proposals:** the dependency plan, the next Litex fact or definition, and the smallest repair suggested by the latest evidence.
- **Litex owns the local checking decision:** it checks the candidate's well-definedness and proof evidence, then either changes the accepted context or leaves it untouched.
- **JSON carries the state transition:** it records the exact candidate, machine result, failed phase or goal, and the evidence needed to choose the next repair.
- **Materialized `.lit` files own the maintained development:** only a contiguous prefix of committed declarations becomes canonical source.
- **Lean is an optional downstream checker:** when a route is supported, trust-free, and actually compiled, Litex evidence can be carried through generated and handwritten adapter layers to an ordinary theorem checked by Lean's kernel.

That produces a real closed loop rather than an “AI-generated” label:

```text
Human fixes the mathematical intent and boundaries
                         ↓
AI proposes the next small Litex fact
                         ↓
Litex checks well-definedness and evidence
          ├─ Committed → context grows → AI proposes the next fact
          └─ RolledBack → context stays fixed
                              ↓
                     structured JSON evidence
                              ↓
                     AI repairs this fact ────────↗

contiguous committed prefix → canonical .lit → clean Litex replay

only when the route is supported and in scope:
Litex evidence → Generated.lean → Adapter.lean → Final.lean → Lean kernel
```

`Accepted` and `Stopped` are useful reader-facing labels for the two branches; the journals preserve the exact transaction states `Committed` and `RolledBack`. A transport-level `ok: true` is not acceptance if the nested `TryStmt.execution.kind` is `RolledBack`.

The quotient-preimage bijection makes this concrete. In [`proof_journals/quotient_preimage_bijection_journal.json`](proof_journals/quotient_preimage_bijection_journal.json), `QPB005A1` rolled back at the local function-unfolding boundary, so the accepted context did not move. The JSON identified that boundary; the AI exposed two smaller equality bridges; `QPB005A5` committed; and only that committed source was later materialized into [`quotient_preimage_bijection.lit`](quotient_preimage_bijection.lit). The AI proposed and repaired, but Litex controlled whether the mathematical context grew.

This repository demonstrates the human–AI–Litex construction loop and its recorded clean Litex gates. It contains no `Generated.lean`, `Adapter.lean`, or `Final.lean` artifact for the Sylow proof, so the Lean line above is the bounded downstream architecture—not a claim that this showcase has already completed that handoff. The reusable, subject-independent protocol is in [`SKILL.md`](SKILL.md).

## Why the JSON journals matter

The JSON journals are the shared working memory between the human, the AI, and the verifier. They are not the final mathematical proof, and they are not a dump of private chain-of-thought. They preserve concise, auditable decision evidence: what was attempted, what the verifier actually reported, why the next edit was chosen, which source eventually committed, and which clean gates later passed.

Field names vary slightly across the development, but the main roles are stable:

| Journal data | What it means |
|---|---|
| `proof_spine` | The shortest natural-language dependency or proof plan fixed before code-level repair. |
| `blocks[].intent` and `dependencies` | The mathematical job of one source-order block and the earlier interfaces it is allowed to use. |
| `attempts[].candidate` | The exact Litex candidate submitted transactionally. |
| `result`, `execution_kind`, and `failed_goal` | Whether the block committed or rolled back, and the earliest goal or phase that failed. |
| `verifier_evidence` | A concise record of the verifier output that justifies the diagnosis. |
| `diagnosis`, `minimal_fix`, and `next_change` | The evidence-backed interpretation and the next smallest proposed repair. |
| `accepted_litex` and `status` | The committed source staged for later materialization, never merely the latest draft. |
| `materialization` and strict gate records | Evidence that committed blocks were written to `.lit` files and checked again from a clean file-backed state. |

For example, block `QPB005` in [`proof_journals/quotient_preimage_bijection_journal.json`](proof_journals/quotient_preimage_bijection_journal.json) first rolled back because a local unary alias did not automatically unfold through the registered two-argument function at fixed `K`. The journal preserved that exact boundary. The repaired candidate exposed the alias-to-function equality and the function-to-coordinate-pair equality as separate bridges; after one further binder-name repair and a checkpoint restart, the transaction committed. The JSON makes that evolution reviewable without polluting the final mathematical `.lit` source with debugging history.

## The mathematical spine

```text
group + homomorphisms + subgroups
              ↓
finite actions + prime arithmetic + Cauchy
              ↓
normalizer N_G(H) and quotient N_G(H)/H
              ↓
prime-order K ≤ N_G(H)/H
              ↓ pull back
P = projection⁻¹(K),   P ≃ K × H
              ↓
|P| = |K||H| = p·p^k = p^(k+1)
              ↓ induction from {1}
p_power_subgroup_exists
```

The deepest local bridge is not the final induction. It is the explicit coordinate bijection for the quotient preimage. The four reconstruction identities live in `quotient_preimage_coordinates.lit`; the typed maps and inverse laws live in `quotient_preimage_bijection.lit`; only then does `quotient_preimage_cardinality.lit` turn the bijection into a product formula.

## The recorded file order

The diagram above is a compressed mathematical overview. The current
`litex.config` exports the following files from top to bottom, matching the
recorded mathematical order, so a later file can use namespaces and facts
established by earlier files:

```text
group → group_homomorphism → subgroup → subgroup_maps → function_inverse → cosets → lagrange → subgroup_structure
→ group_actions → normal_subgroup → quotient_groups → finite_function_spaces → prime_arithmetic → prime_power_factors
→ p_group_actions → cyclic_group → cauchy_tuples → cauchy_restriction → cauchy_rotation → cauchy_fixed_points → cauchy_power_hom → cauchy_theorem
→ normalizer → sylow_coset_action → normalizer_quotient → quotient_preimage → quotient_preimage_coordinates → quotient_preimage_bijection → quotient_preimage_cardinality → sylow_successor → sylow
```

That is the complete recorded mathematical prefix. The [`accepted/`](accepted/), [`checkpoints/`](checkpoints/), and [`replay/`](replay/) directories preserve evidence-only Litex artifacts; none of them is a premise of the root theorem.

The JSON journals below preserve successful creation-time gates from the Litex
build used to construct this proof. The snapshot is now a configured module,
but the current manifest has not established a green current-HEAD replay. The
last compatibility assessment found that the unchanged legacy `.lit` source
no longer completed under the then-current verifier: the earliest direct
`group.lit` gate reported the well-definedness error
`obj group.mul(group.inv(a), a) is not in r`, and the final-file prefix exposed
an existing nonempty-carrier incompatibility in `subgroup_structure.lit`. The
recorded success is therefore versioned workflow evidence, not a claim that
current `HEAD` re-verifies the unchanged proof. Porting the mathematical source
is separate work.

## AI + Litex: the working protocol

The agent does not send a whole chapter to the verifier and hope for a yes/no answer. It advances one declaration and one file at a time:

1. Freeze the mathematical statement and its exact earlier-file citations.
2. Load a persistent file-backed session at the latest verified checkpoint.
3. Submit the next declaration inside one literal outer `try:` block.
4. Parse the nested transaction result: transport `ok: true` can still contain `TryStmt.execution.kind = RolledBack`.
5. Journal the exact candidate, failed phase/goal, and diagnosis before changing it.
6. Repair the earliest local failure in the same session; a commit becomes the next checkpoint.
7. Materialize only committed declarations, mirror the file, and perform a clean file-backed replay.
8. At the end, run strict verification on the final file and on the complete replay module.

A representative repair occurred in the preimage bijection. The first candidate treated a fixed-K local function alias as if it unfolded automatically; the transaction rolled back. The accepted candidate exposed the local alias, the registered two-argument function, and the coordinate pair as separate equalities. The proof then committed and the final cardinality consumer shrank to a short equality chain.

## Proof journal walkthrough

The ordered teaching steps below preserve the former presentation in Markdown. The mathematics lens follows the constructions; the AI-systems lens follows citations, `try` frames, JSON rollback/commit states, materialization, and gates.

### 01 / theorem: Start with the mathematical claim

**Mathematics.** Let H and K be ordinary subgroups of a group G. Their intersection contains the identity, and it is closed under multiplication and inverse; therefore it is a subgroup. Nothing about conjugation or normality is used.

**AI system.** Freeze the exact theorem statement before proof search. The statement is the stable contract; candidate bodies may change transactionally without changing the mathematics.


```litex
thm subgroup_intersection_closed:
    ? forall G nonempty_set, group &group::Group<G>, H, K power_set(G):
        $is_subgroup(G, group, H)
        $is_subgroup(G, group, K)
        =>:
            $is_subgroup(G, group, {x G: x $in H and x $in K})
```

Structured evidence:


```json
{
  "claim": "The same theorem header appears in every B005 attempt and in subgroup.lit."
}
```

### 02 / cite: Bring only the visible dependency surface

**Mathematics.** Chapter 9 needs a carrier G together with multiplication, identity, inverse, and the group laws. Chapter 2 already packages exactly these data as Group<G>.

**AI system.** Do not recreate group operations or pretend Mathlib is available. The module order registers group.lit first, so Chapter 9 cites group::Group and every dependency stays inspectable.


```litex
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
```

Structured evidence:


```json
{
  "citation": "Visible Chapter 2 interface",
  "path": "../group.lit",
  "declarations": [
    "group::Group",
    "group::group_laws",
    "group::divides"
  ]
}
```

### 02b / homomorphisms: Build the first Chapter 9 dependency layer

**Mathematics.** A group homomorphism is a supplied function that preserves identity and multiplication. Multiplication preservation is definitional; inverse preservation follows because the image of x⁻¹ multiplies with the image of x to give the target identity.

**AI system.** GH001-GH005 were submitted in one persistent framed session. The bodyless inverse theorem rolled back at its exact equality goal; the explicit cancellation calculation then committed, was materialized in its own file, and passed a cold strict gate.


```litex
thm group_hom_map_inv:
    ? forall G, H nonempty_set, source &group::Group<G>, target &group::Group<H>, f fn(x G) H, x G:
        $is_group_hom(G, H, source, target, f)
        =>:
            f(source.inv(x)) = target.inv(f(x))
    by def $group::group_laws(H, target.mul, target.one, target.inv)
    source.mul(source.inv(x), x) = source.one
    target.mul(f(source.inv(x)), f(x)) = f(source.mul(source.inv(x), x)) = f(source.one) = target.one
    release thm group::mul_inv_cancel(H, target.mul, target.one, target.inv, f(x))
    target.mul(f(x), target.inv(f(x))) = target.one
    release thm group::mul_one(H, target.mul, target.one, target.inv, f(source.inv(x)))
    f(source.inv(x)) = target.mul(f(source.inv(x)), target.one) = target.mul(f(source.inv(x)), target.mul(f(x), target.inv(f(x))))
    target.mul(f(source.inv(x)), target.mul(f(x), target.inv(f(x)))) = target.mul(target.mul(f(source.inv(x)), f(x)), target.inv(f(x)))
    target.mul(target.mul(f(source.inv(x)), f(x)), target.inv(f(x))) = target.mul(target.one, target.inv(f(x))) = target.inv(f(x))
```

Structured evidence:


```json
{
  "block": "GH005",
  "status": "materialized",
  "attempts": [
    {
      "result": "rejected_rolled_back",
      "failed_phase": "verification",
      "verifier_evidence": "Session request GH005A1 returned a RolledBack TryStmt: cannot prove then-clause; failed goal f(source.inv(x)) = target.inv(f(x))."
    },
    {
      "result": "accepted",
      "verifier_evidence": "Session request GH005A2 returned ok:true; the TryStmt committed a DefThmStmt, every execution phase succeeded, and the final equality was discharged by the known equality path."
    }
  ],
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "target": "file",
    "statement_count": 15,
    "outcomes": [
      "success"
    ],
    "strict_mode": true,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 03 / model: Define the Chapter 9 concept once

**Mathematics.** A subset H is a subgroup when it contains the identity and is closed under the group multiplication and inverse operations.

**AI system.** B001 is submitted as one outer try transaction. It commits a reusable proposition against group::Group; later blocks refer to the stored fact interface instead of unfolding ad hoc copies.


```litex
prop is_subgroup(G nonempty_set, group &group::Group<G>, H power_set(G)):
    group.one $in H
    forall x, y G:
        x $in H
        y $in H
        =>:
            group.mul(x, y) $in H
    forall x G:
        x $in H
        =>:
            group.inv(x) $in H
```

Structured evidence:


```json
{
  "block": "B001",
  "status": "materialized",
  "result": "accepted",
  "verifier_evidence": "session block B001 returned ok: true; TryStmt execution kind: Committed; inner result kind: DefPropStmt"
}
```

### 04 / try: Submit the natural proof first

**Mathematics.** The first proof spells out membership in H and K, proves componentwise closure, constructs intersection membership, and folds the subgroup definition.

**AI system.** B005-A1 commits. Acceptance is not the end of authoring: it establishes a safe upper bound from which the AI can run deletion probes without risking the accepted prefix.


```litex
try:
    thm subgroup_intersection_closed:
        ? forall G nonempty_set, group &group::Group<G>, H, K power_set(G):
            $is_subgroup(G, group, H)
            $is_subgroup(G, group, K)
            =>:
                $is_subgroup(G, group, {x G: x $in H and x $in K})
        group.one $in H
        group.one $in K
        group.one $in {x G: x $in H and x $in K}
        claim:
            ? forall x, y {q G: q $in H and q $in K}:
                group.mul(x, y) $in {q G: q $in H and q $in K}
            x $in H
            x $in K
            y $in H
            y $in K
            group.mul(x, y) $in H
            group.mul(x, y) $in K
            release thm set_builder_member(group.mul(x, y), {q G: q $in H and q $in K})
        claim:
            ? forall x {q G: q $in H and q $in K}:
                group.inv(x) $in {q G: q $in H and q $in K}
            x $in H
            x $in K
            group.inv(x) $in H
            group.inv(x) $in K
            release thm set_builder_member(group.inv(x), {q G: q $in H and q $in K})
        by def:
            ? $is_subgroup(G, group, {x G: x $in H and x $in K})
```

Structured evidence:


```json
{
  "attempt_id": "B005-A1",
  "parent_attempt_id": null,
  "result": "accepted_provisional",
  "verifier_evidence": "session block B005-A1 returned ok: true; TryStmt execution kind: Committed; inner result kind: DefThmStmt",
  "diagnosis": "Current inference constructs the identity's set-builder membership from the two component membership facts; the expected missing-bridge failure does not exist.",
  "next_change": "Restart, replay B001-B004, and deletion-probe the explicit closure proof instead of preserving verifier-redundant lines."
}
```

### 05 / JSON: Read the transaction, not just ok

**Mathematics.** Deleting the whole proof body removes all three closure witnesses. The theorem is true, but the current local facts no longer prove it.

**AI system.** The framed request itself reports ok: true, yet the nested TryStmt says RolledBack and verify_process says Error. A robust agent parses the transaction state and failed_goal instead of treating transport success as proof success.


```litex
try:
    thm subgroup_intersection_closed:
        ? forall G nonempty_set, group &group::Group<G>, H, K power_set(G):
            $is_subgroup(G, group, H)
            $is_subgroup(G, group, K)
            =>:
                $is_subgroup(G, group, {x G: x $in H and x $in K})
```

Structured evidence:


```json
{
  "attempt_id": "B005-A2",
  "parent_attempt_id": "B005-A1",
  "result": "failed",
  "failed_phase": "proof",
  "verifier_evidence": "session event ok: true, but TryStmt execution kind: RolledBack; failed_goal: $is_subgroup(G, group, {x G: x $in H and x $in K}); verify_process: Error; message: thm `subgroup_intersection_closed` failed: cannot prove then-clause",
  "diagnosis": "Protocol-level ok does not mean the candidate committed; the AI must inspect execution.kind and the nested phase result.",
  "minimal_fix": "Add the identity, multiplication-closure, and inverse-closure goals as a minimal mathematical skeleton, then fold is_subgroup.",
  "next_change": "Submit only the three closure obligations and by def, leaving their internal facts to current inference."
}
```

### 06 / repair: Locate the nested-scope boundary

**Mathematics.** Naming the three closure goals is still insufficient: inside the multiplication claim, the component closure results must become explicit facts before membership in the intersection can be concluded.

**AI system.** B005-A3 narrows the failure from the whole theorem to one exact failed_goal. This is the useful repair coordinate: add component closure facts inside the nested claim, not a large generic proof script.


```litex
try:
    thm subgroup_intersection_closed:
        ? forall G nonempty_set, group &group::Group<G>, H, K power_set(G):
            $is_subgroup(G, group, H)
            $is_subgroup(G, group, K)
            =>:
                $is_subgroup(G, group, {x G: x $in H and x $in K})
        group.one $in {x G: x $in H and x $in K}
        claim:
            ? forall x, y {q G: q $in H and q $in K}:
                group.mul(x, y) $in {q G: q $in H and q $in K}
        claim:
            ? forall x {q G: q $in H and q $in K}:
                group.inv(x) $in {q G: q $in H and q $in K}
        by def:
            ? $is_subgroup(G, group, {x G: x $in H and x $in K})
```

Structured evidence:


```json
{
  "attempt_id": "B005-A3",
  "parent_attempt_id": "B005-A2",
  "result": "failed",
  "failed_phase": "proof",
  "verifier_evidence": "TryStmt execution kind: RolledBack; failed_goal: group.mul(x, y) $in {q G: q $in H and q $in K}; verify_process: Error; message: claim failed: cannot prove then-clause",
  "diagnosis": "The three-obligation skeleton is mathematically right, but nested claim scopes need explicit component facts before the set-builder target becomes inferable.",
  "minimal_fix": "Inside each nested claim, expose membership in H and K and the corresponding closure results; deletion-probe the explicit set_builder_member releases separately.",
  "next_change": "Add component membership and component closure facts, while omitting the old explicit set-builder releases."
}
```

### 07 / accept: Keep the mathematical spine, remove the echoes

**Mathematics.** The final body displays exactly the identity, multiplication, and inverse obligations. Within the two nested claims it records the H and K closure conclusions needed to build intersection membership.

**AI system.** B005-A5 commits after deletion probes. Refined-set membership and set-builder construction are supplied by current inference, so the materialized source omits the historical membership and release echoes while retaining the proof's reviewable structure.


```litex
try:
    thm subgroup_intersection_closed:
        ? forall G nonempty_set, group &group::Group<G>, H, K power_set(G):
            $is_subgroup(G, group, H)
            $is_subgroup(G, group, K)
            =>:
                $is_subgroup(G, group, {x G: x $in H and x $in K})
        group.one $in {x G: x $in H and x $in K}
        claim:
            ? forall x, y {q G: q $in H and q $in K}:
                group.mul(x, y) $in {q G: q $in H and q $in K}
            group.mul(x, y) $in H
            group.mul(x, y) $in K
        claim:
            ? forall x {q G: q $in H and q $in K}:
                group.inv(x) $in {q G: q $in H and q $in K}
            group.inv(x) $in H
            group.inv(x) $in K
        by def:
            ? $is_subgroup(G, group, {x G: x $in H and x $in K})
```

Structured evidence:


```json
{
  "attempt_id": "B005-A5",
  "parent_attempt_id": "B005-A4",
  "result": "accepted",
  "verifier_evidence": "session block B005-A5 returned ok: true; TryStmt execution kind: Committed; inner result kind: DefThmStmt; verify_process: Success",
  "diagnosis": "Refined-set parameters already expose membership in H and K. The irreducible readable proof surface is the three closure obligations plus the two component closure results inside each nested claim.",
  "minimal_fix": "Accepted as the materialization candidate; retain the mathematical skeleton and remove verifier-redundant membership and release echoes.",
  "next_change": "Materialize the contiguous B001-B005 prefix and run the strict registered-file gate."
}
```

### 08 / source: Materialize only the accepted prefix

**Mathematics.** The checked file now contains the subgroup definition, its two direct projection theorems, the intersection construction, and the closure theorem in dependency order.

**AI system.** The journal remains the staging source until B001-B005 are all accepted. Only accepted_litex is copied into subgroup.lit; provisional and rolled-back candidates remain evidence, never production source.


```litex
thm subgroup_intersection_closed:
    ? forall G nonempty_set, group &group::Group<G>, H, K power_set(G):
        $is_subgroup(G, group, H)
        $is_subgroup(G, group, K)
        =>:
            $is_subgroup(G, group, {x G: x $in H and x $in K})
    group.one $in {x G: x $in H and x $in K}
    claim:
        ? forall x, y {q G: q $in H and q $in K}:
            group.mul(x, y) $in {q G: q $in H and q $in K}
        group.mul(x, y) $in H
        group.mul(x, y) $in K
    claim:
        ? forall x {q G: q $in H and q $in K}:
            group.inv(x) $in {q G: q $in H and q $in K}
        group.inv(x) $in H
        group.inv(x) $in K
    by def:
        ? $is_subgroup(G, group, {x G: x $in H and x $in K})
```

Structured evidence:


```json
{
  "block_ids": [
    "B001",
    "B002",
    "B003",
    "B004",
    "B005"
  ],
  "target": "scripts/ai_litex_sylow/subgroup.lit",
  "replay_mirror": "scripts/ai_litex_sylow/web/replay/subgroup.lit",
  "source_policy": "accepted_litex only; replay mirror must byte-match the root source"
}
```

### 09 / gate: Close with an independent strict run

**Mathematics.** The final theorem is checked again from a cold registered-file path together with its Chapter 2 dependency, independently of the live proof session.

**AI system.** The strict summary must exit 0 and report no direct trust, axioms, trusted object assumptions, or unverified imports. Session speed and final dependency verification are separate claims.


```text
Independent strict check: success
direct trust: 0
axioms: 0
trusted object assumptions: 0
unverified imports: none
```

Structured evidence:


```json
{
  "result": "success",
  "process_exit_code": 0,
  "output_type": "strict full run",
  "statement_count": 15,
  "direct_trust": 0,
  "axioms": 0,
  "trusted_object_assumptions": 0,
  "unverified_imports": []
}
```

### 10 / transport layer: Transport subgroups along homomorphisms

**Mathematics.** The image follows explicit source witnesses; the comap, kernel, and range reuse the same three subgroup obligations through the homomorphism laws.

**AI system.** SM006 first committed in source form, then a fresh-session deletion probe removed redundant set-builder echoes. A whole-proof deletion rolled back at the image-subgroup goal, so the smaller retained witness proof is demonstrably live.


```litex
thm subgroup_map_closed:
    ? forall G, H nonempty_set, source &group::Group<G>, target &group::Group<H>, f fn(x G) H, S power_set(G):
        $group_homomorphism::is_group_hom(G, H, source, target, f)
        $subgroup::is_subgroup(G, source, S)
        =>:
            $subgroup::is_subgroup(H, target, \subgroup_map<G, H, f>(S))
    \subgroup_map<G, H, f>(S) = {y H: $has_subgroup_map_preimage(G, H, f, S, y)}
    witness $has_subgroup_map_preimage(G, H, f, S, target.one) from source.one
    claim:
        ? forall a, b H:
            a $in \subgroup_map<G, H, f>(S)
            b $in \subgroup_map<G, H, f>(S)
            =>:
                target.mul(a, b) $in \subgroup_map<G, H, f>(S)
        by def $has_subgroup_map_preimage(G, H, f, S, a)
        obtain x from $has_subgroup_map_preimage(G, H, f, S, a)
        by def $has_subgroup_map_preimage(G, H, f, S, b)
        obtain y from $has_subgroup_map_preimage(G, H, f, S, b)
        witness $has_subgroup_map_preimage(G, H, f, S, target.mul(a, b)) from source.mul(x, y):
            f(source.mul(x, y)) = target.mul(f(x), f(y)) = target.mul(a, b)
    claim:
        ? forall a H:
            a $in \subgroup_map<G, H, f>(S)
            =>:
                target.inv(a) $in \subgroup_map<G, H, f>(S)
        by def $has_subgroup_map_preimage(G, H, f, S, a)
        obtain x from $has_subgroup_map_preimage(G, H, f, S, a)
        release thm group_homomorphism::group_hom_map_inv(G, H, source, target, f, x)
        witness $has_subgroup_map_preimage(G, H, f, S, target.inv(a)) from source.inv(x):
            f(source.inv(x)) = target.inv(f(x)) = target.inv(a)
    by def $subgroup::is_subgroup(H, target, \subgroup_map<G, H, f>(S))
```

Structured evidence:


```json
{
  "block": "SM006",
  "status": "materialized",
  "attempts": [
    {
      "result": "accepted_provisional",
      "verifier_evidence": "Session SM006A1 committed subgroup_map_closed; session artifacts list it as a checked theorem with the intended cross-file dependencies.",
      "diagnosis": "Preimage witnesses supply source subgroup members; multiplication and inverse closure transport those witnesses through the homomorphism."
    },
    {
      "result": "accepted",
      "verifier_evidence": "Fresh prefix session SM006D1 committed subgroup_map_closed with SuccessVerifyTheoremResult.",
      "diagnosis": "A successful existential witness already lets Litex reconstruct membership in the defining set builder and transport it across the image equality."
    },
    {
      "result": "rejected_rolled_back",
      "verifier_evidence": "Fresh prefix session SM006LIVE0 returned TryStmt.execution.kind RolledBack and failed_goal equal to the image-subgroup conclusion.",
      "diagnosis": "The conclusion is not already available from imports, definitions, or builtin inference; the retained witness proof is live."
    }
  ],
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "statement_count": 29,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 11 / choice layer: Make coset representative choice explicit

**Mathematics.** Every target gets a nonempty fiber containing real preimages or the displayed default. One explicit axiom-of-choice step selects a total inverse, whose specification later certifies coset representatives.

**AI system.** FI009 committed the complete choice construction. Deleting its entire body in a fresh prefix session rolled back at the existential total-inverse goal, while the independent strict file gate succeeded.


```litex
thm total_inverse_exists:
    ? forall S nonempty_set, T set, default S, f fn(x S) T:
        exist inverse fn(y T) S st {$is_total_inverse(S, T, default, f, inverse)}
    claim:
        ? forall A \inverse_fiber_family<S, T, default, f>:
            $is_nonempty_set(A)
        A $in {B power_set(S): $is_inverse_fiber(S, T, default, f, B)}
        by def $is_inverse_fiber(S, T, default, f, A)
        obtain y from $is_inverse_fiber(S, T, default, f, A)
        release thm inverse_fiber_nonempty(S, T, default, f, y)
        $is_nonempty_set(\inverse_fiber<S, T, default, f>(y))
    by axiom_of_choice: set \inverse_fiber_family<S, T, default, f>:
        forall A \inverse_fiber_family<S, T, default, f>:
            $is_nonempty_set(A)
    obtain chooser from exist c fn(A \inverse_fiber_family<S, T, default, f>) big_union(\inverse_fiber_family<S, T, default, f>) st {$is_choice_function_for(\inverse_fiber_family<S, T, default, f>, \inverse_fiber_family<S, T, default, f>, fn(A \inverse_fiber_family<S, T, default, f>) \inverse_fiber_family<S, T, default, f> {A}, c)}
    thm chooser_mem:
        ? forall A \inverse_fiber_family<S, T, default, f>:
            chooser(A) $in A
    claim:
        ? forall y T:
            \inverse_fiber<S, T, default, f>(y) $in \inverse_fiber_family<S, T, default, f>
        witness $is_inverse_fiber(S, T, default, f, \inverse_fiber<S, T, default, f>(y)) from y
        release thm set_builder_member(\inverse_fiber<S, T, default, f>(y), {A power_set(S): $is_inverse_fiber(S, T, default, f, A)})
        \inverse_fiber<S, T, default, f>(y) $in {A power_set(S): $is_inverse_fiber(S, T, default, f, A)}
        \inverse_fiber_family<S, T, default, f> = {A power_set(S): $is_inverse_fiber(S, T, default, f, A)}
    claim:
        ? forall y T:
            chooser(\inverse_fiber<S, T, default, f>(y)) $in \inverse_fiber<S, T, default, f>(y)
        release thm chooser_mem(\inverse_fiber<S, T, default, f>(y))
    claim:
        ? forall y T:
            chooser(\inverse_fiber<S, T, default, f>(y)) $in S
        chooser(\inverse_fiber<S, T, default, f>(y)) $in \inverse_fiber<S, T, default, f>(y)
        \inverse_fiber<S, T, default, f>(y) = {x S: $inverse_fiber_member(S, T, default, f, y, x)}
        chooser(\inverse_fiber<S, T, default, f>(y)) $in {x S: $inverse_fiber_member(S, T, default, f, y, x)}
    claim:
        ? forall y T:
            $has_preimage(S, T, f, y)
            =>:
                f(chooser(\inverse_fiber<S, T, default, f>(y))) = y
        chooser(\inverse_fiber<S, T, default, f>(y)) $in \inverse_fiber<S, T, default, f>(y)
        \inverse_fiber<S, T, default, f>(y) = {x S: $inverse_fiber_member(S, T, default, f, y, x)}
        chooser(\inverse_fiber<S, T, default, f>(y)) $in {x S: $inverse_fiber_member(S, T, default, f, y, x)}
        by def $inverse_fiber_member(S, T, default, f, y, chooser(\inverse_fiber<S, T, default, f>(y)))
        by cases:
            ? f(chooser(\inverse_fiber<S, T, default, f>(y))) = y
            case f(chooser(\inverse_fiber<S, T, default, f>(y))) = y:
                f(chooser(\inverse_fiber<S, T, default, f>(y))) = y
            case $is_default_inverse_fiber_member(S, T, default, f, y, chooser(\inverse_fiber<S, T, default, f>(y))):
                by def $is_default_inverse_fiber_member(S, T, default, f, y, chooser(\inverse_fiber<S, T, default, f>(y)))
                impossible $has_preimage(S, T, f, y)
    claim:
        ? forall y T:
            not $has_preimage(S, T, f, y)
            =>:
                chooser(\inverse_fiber<S, T, default, f>(y)) = default
        chooser(\inverse_fiber<S, T, default, f>(y)) $in \inverse_fiber<S, T, default, f>(y)
        \inverse_fiber<S, T, default, f>(y) = {x S: $inverse_fiber_member(S, T, default, f, y, x)}
        chooser(\inverse_fiber<S, T, default, f>(y)) $in {x S: $inverse_fiber_member(S, T, default, f, y, x)}
        by def $inverse_fiber_member(S, T, default, f, y, chooser(\inverse_fiber<S, T, default, f>(y)))
        by cases:
            ? chooser(\inverse_fiber<S, T, default, f>(y)) = default
            case f(chooser(\inverse_fiber<S, T, default, f>(y))) = y:
                witness $has_preimage(S, T, f, y) from chooser(\inverse_fiber<S, T, default, f>(y))
                impossible not $has_preimage(S, T, f, y)
            case $is_default_inverse_fiber_member(S, T, default, f, y, chooser(\inverse_fiber<S, T, default, f>(y))):
                by def $is_default_inverse_fiber_member(S, T, default, f, y, chooser(\inverse_fiber<S, T, default, f>(y)))
                chooser(\inverse_fiber<S, T, default, f>(y)) = default
    have fn chosen_inverse(y T) S = chooser(\inverse_fiber<S, T, default, f>(y))
    claim:
        ? $is_total_inverse(S, T, default, f, chosen_inverse)
        claim:
            ? forall y T:
                $has_preimage(S, T, f, y)
                =>:
                    f(chosen_inverse(y)) = y
            chosen_inverse(y) = chooser(\inverse_fiber<S, T, default, f>(y))
            f(chosen_inverse(y)) = f(chooser(\inverse_fiber<S, T, default, f>(y))) = y
        claim:
            ? forall y T:
                not $has_preimage(S, T, f, y)
                =>:
                    chosen_inverse(y) = default
            chosen_inverse(y) = chooser(\inverse_fiber<S, T, default, f>(y)) = default
        by def $is_total_inverse(S, T, default, f, chosen_inverse)
    witness exist inverse fn(y T) S st {$is_total_inverse(S, T, default, f, inverse)} from chosen_inverse
```

Structured evidence:


```json
{
  "block": "FI009",
  "status": "materialized",
  "attempts": [
    {
      "result": "accepted",
      "verifier_evidence": "FI009A1 committed total_inverse_exists with SuccessVerifyTheoremResult; the choice family, chooser, totality clauses, and existential witness all verified."
    },
    {
      "result": "rejected_rolled_back",
      "verifier_evidence": "Fresh prefix session FI009LIVE0 rolled back at the existential total-inverse goal.",
      "diagnosis": "The selected inverse is not supplied by imports or builtin inference; the explicit choice construction is live."
    }
  ],
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "statement_count": 47,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 12 / cosets: Turn a finite group into quotient coordinates

**Mathematics.** Each element g has a left coset gH, a chosen representative r(gH), and a residual coordinate r(gH)⁻¹g in H. Multiplication reconstructs g, while coset equality reconstructs both coordinates, giving an explicit bijection G ≃ (G/H) × H.

**AI system.** C001-C023 were committed in source order in one persistent session. A fresh namespaced checkpoint containing C001-C022 made the bodyless C023 statement well formed, then the exact bijection goal rolled back; the materialized proof subsequently passed strict file and module gates.


```litex
thm left_coset_forward_bijective:
    ? forall G nonempty_set, group &group::Group<G>, H power_set(G):
        $subgroup::is_subgroup(G, group, H)
        =>:
            $bijective(G, cart(\quotient_group_carrier<G, group>(H), H), \left_coset_forward<G, group, H>)
    claim:
        ? $function_inverse::is_left_inverse(G, cart(\quotient_group_carrier<G, group>(H), H), \left_coset_forward<G, group, H>, \left_coset_backward<G, group, H>)
        claim:
            ? forall g G:
                \left_coset_backward<G, group, H>(\left_coset_forward<G, group, H>(g)) = g
            release thm left_coset_backward_forward(G, group, H, g)
        by def $function_inverse::is_left_inverse(G, cart(\quotient_group_carrier<G, group>(H), H), \left_coset_forward<G, group, H>, \left_coset_backward<G, group, H>)
    release thm function_inverse::injective_of_left_inverse(G, cart(\quotient_group_carrier<G, group>(H), H), \left_coset_forward<G, group, H>, \left_coset_backward<G, group, H>)
    claim:
        ? $function_inverse::is_right_inverse(G, cart(\quotient_group_carrier<G, group>(H), H), \left_coset_forward<G, group, H>, \left_coset_backward<G, group, H>)
        claim:
            ? forall pair cart(\quotient_group_carrier<G, group>(H), H):
                \left_coset_forward<G, group, H>(\left_coset_backward<G, group, H>(pair)) = pair
            release thm left_coset_forward_backward(G, group, H, pair)
        by def $function_inverse::is_right_inverse(G, cart(\quotient_group_carrier<G, group>(H), H), \left_coset_forward<G, group, H>, \left_coset_backward<G, group, H>)
    release thm function_inverse::surjective_of_right_inverse(G, cart(\quotient_group_carrier<G, group>(H), H), \left_coset_forward<G, group, H>, \left_coset_backward<G, group, H>)
    by def $bijective(G, cart(\quotient_group_carrier<G, group>(H), H), \left_coset_forward<G, group, H>)
```

Structured evidence:


```json
{
  "block": "C023",
  "status": "materialized",
  "accepted_attempt": {
    "result": "accepted",
    "verifier_evidence": "C023A1 committed SuccessVerifyTheoremResult."
  },
  "liveness_probe": {
    "attempt_id": "C023D3",
    "candidate": "The final bijection theorem with its entire proof body deleted, citing the namespaced C001-C022 checkpoint.",
    "transport_ok": true,
    "execution_kind": "RolledBack",
    "verify_well_definedness": "Success",
    "verify_process": "Error",
    "failed_goal": "$bijective(G, cart(quotient_group_carrier(H), H), left_coset_forward)",
    "diagnosis": "The final bijection is not an imported or automatically available fact; its two inverse proofs are live. Earlier unqualified probes also documented that replay checkpoints are module namespaces, not textual includes."
  },
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "statement_count": 96,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 13 / Lagrange: Read the coordinate bijection as divisibility

**Mathematics.** For finite G and H, the checked bijection gives |G| = |G/H| |H|. The quotient size is therefore a concrete divisibility witness; a separate finite-cardinality argument shows that a subgroup of order one is exactly {1}.

**AI system.** Both theorems committed inside literal outer try transactions. In a fresh session the bodyless Lagrange statement remained well formed but rolled back at the exact divisibility goal, then the two-block file passed strict file and complete-cabinet gates.


```litex
thm subgroup_order_divides_group_order:
    ? forall G nonempty_set, group &group::Group<G>, H power_set(G):
        $subgroup::is_subgroup(G, group, H)
        $is_finite_set(G)
        $is_finite_set(H)
        =>:
            $group::divides(finite_set_size(H), finite_set_size(G))
    release thm cosets::left_coset_space_finite(G, group, H)
    release thm cosets::left_coset_forward_bijective(G, group, H)
    $is_finite_set(cart(\cosets::quotient_group_carrier<G, group>(H), H))
    finite_set_size(G) = finite_set_size(cart(\cosets::quotient_group_carrier<G, group>(H), H))
    finite_set_size(cart(\cosets::quotient_group_carrier<G, group>(H), H)) = finite_set_size(\cosets::quotient_group_carrier<G, group>(H)) * finite_set_size(H)
    finite_set_size(G) = finite_set_size(\cosets::quotient_group_carrier<G, group>(H)) * finite_set_size(H) = finite_set_size(H) * finite_set_size(\cosets::quotient_group_carrier<G, group>(H))
    witness $group::divides(finite_set_size(H), finite_set_size(G)) from finite_set_size(\cosets::quotient_group_carrier<G, group>(H)):
        finite_set_size(G) = finite_set_size(H) * finite_set_size(\cosets::quotient_group_carrier<G, group>(H))
```

Structured evidence:


```json
{
  "block": "L001",
  "status": "materialized",
  "accepted_attempt": {
    "attempt_id": "L001A1",
    "result": "accepted",
    "verifier_evidence": "Literal outer try committed; SuccessVerifyTheoremResult."
  },
  "liveness_probe": {
    "attempt_id": "L001D1",
    "candidate": "subgroup_order_divides_group_order with the complete proof body deleted under a fresh theorem name",
    "transport_ok": true,
    "execution_kind": "RolledBack",
    "verify_well_definedness": "Success",
    "verify_process": "Error",
    "failed_goal": "$group::divides(finite_set_size(H), finite_set_size(G))",
    "diagnosis": "Lagrange divisibility is not supplied by an import or a builtin theorem; the explicit coset-cardinality argument is live."
  },
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "statement_count": 99,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 14 / inherited structure: Run Lagrange inside a subgroup

**Mathematics.** The ambient multiplication, identity, and inverse restrict to any subgroup B and satisfy the same group laws. If A is a subgroup with A ⊆ B, then A is a subgroup of that inherited group, so Lagrange inside B gives |A| ∣ |B|.

**AI system.** SS001-SS010 committed in source order. The cross-file carrier alias was kept explicit as subgroup_carrier = H while operation return types expose H directly; the final nested-divisibility theorem then committed. A fresh bodyless probe was well formed but rolled back at the exact divisibility goal.


```litex
thm subgroup_order_divides_subgroup_order:
    ? forall G nonempty_set, group &group::Group<G>, A, B power_set(G):
        $subgroup::is_subgroup(G, group, A)
        $subgroup::is_subgroup(G, group, B)
        A $subset B
        $is_finite_set(A)
        $is_finite_set(B)
        =>:
            $group::divides(finite_set_size(A), finite_set_size(B))
    release thm nested_subgroup_closed(G, group, A, B)
    release thm lagrange::subgroup_order_divides_group_order(\subgroup_carrier<G, group, B>, \subgroup_group<G, group, B>, A)
    \subgroup_carrier<G, group, B> = B
    finite_set_size(\subgroup_carrier<G, group, B>) = finite_set_size(B)
```

Structured evidence:


```json
{
  "block": "SS010",
  "status": "materialized",
  "accepted_attempt": {
    "attempt_id": "SS010A1",
    "result": "accepted",
    "verifier_evidence": "Outer try committed after citing nested_subgroup_closed and lagrange::subgroup_order_divides_group_order inside B."
  },
  "liveness_probe": {
    "id": "SS010D1",
    "statement": "bodyless subgroup_order_divides_subgroup_order_liveness",
    "result": "rejected_rolled_back",
    "verify_well_definedness": "Success",
    "verify_process": "Error",
    "failed_goal": "$group::divides(finite_set_size(A), finite_set_size(B))",
    "meaning": "The conclusion is not a pre-existing imported fact; the accepted SS010 body supplies the proof."
  },
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "statement_count": 118,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 15 / group actions: Expose orbit-stabilizer as an explicit bijection

**Mathematics.** For a group action and a point x, choose one group representative for every point of orbit(x). Every g then splits into its orbit point and a residual element of stabilizer(x); multiplication reconstructs g, and the two coordinate maps are inverse.

**AI system.** GA001-GA021 were committed as source-order transactions. The final theorem cites the two inverse laws through the visible function-inverse interface. Deleting its proof body leaves a well-formed bijection goal that rolls back, while the materialized file passes strict file and complete-module gates.


```litex
thm orbit_stabilizer_forward_bijective:
    ? forall G nonempty_set, X set, group &group::Group<G>, act fn(g G, x X) X, x X:
        $is_group_action(G, X, group, act)
        =>:
            $bijective(G, cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)), \orbit_stabilizer_forward<G, X, group, act, x>)
    claim:
        ? $function_inverse::is_left_inverse(G, cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)), \orbit_stabilizer_forward<G, X, group, act, x>, \orbit_stabilizer_backward<G, X, group, act, x>)
        claim:
            ? forall g G:
                \orbit_stabilizer_backward<G, X, group, act, x>(\orbit_stabilizer_forward<G, X, group, act, x>(g)) = g
            release thm orbit_stabilizer_backward_forward(G, X, group, act, x, g)
        by def $function_inverse::is_left_inverse(G, cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)), \orbit_stabilizer_forward<G, X, group, act, x>, \orbit_stabilizer_backward<G, X, group, act, x>)
    release thm function_inverse::injective_of_left_inverse(G, cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)), \orbit_stabilizer_forward<G, X, group, act, x>, \orbit_stabilizer_backward<G, X, group, act, x>)
    claim:
        ? $function_inverse::is_right_inverse(G, cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)), \orbit_stabilizer_forward<G, X, group, act, x>, \orbit_stabilizer_backward<G, X, group, act, x>)
        claim:
            ? forall pair cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)):
                \orbit_stabilizer_forward<G, X, group, act, x>(\orbit_stabilizer_backward<G, X, group, act, x>(pair)) = pair
            release thm orbit_stabilizer_forward_backward(G, X, group, act, x, pair)
        by def $function_inverse::is_right_inverse(G, cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)), \orbit_stabilizer_forward<G, X, group, act, x>, \orbit_stabilizer_backward<G, X, group, act, x>)
    release thm function_inverse::surjective_of_right_inverse(G, cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)), \orbit_stabilizer_forward<G, X, group, act, x>, \orbit_stabilizer_backward<G, X, group, act, x>)
    by def $bijective(G, cart(\orbit<G, X, act>(x), \stabilizer<G, X, act, group.one>(x)), \orbit_stabilizer_forward<G, X, group, act, x>)
```

Structured evidence:


```json
{
  "block": "GA021",
  "status": "materialized",
  "accepted_attempt": {
    "attempt_id": "GA021A1",
    "result": "accepted",
    "verifier_evidence": "Literal outer try committed the explicit bijection from the proved left and right inverse laws; all three phases reported Success."
  },
  "liveness_probe": {
    "frame_id": "GA_LIVENESS",
    "result": "rejected_rolled_back",
    "verify_well_definedness": "Success",
    "verify_process": "Error",
    "affect_environment": "NotRun",
    "failed_goal": "$bijective(G, cart(orbit(x), stabilizer(x)), orbit_stabilizer_forward)",
    "diagnosis": "The final bijection statement is meaningful but is not automatically available when its proof body is deleted."
  },
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "statement_count": 139,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 16 / normal layer: Add exactly what normality contributes

**Mathematics.** A normal subgroup is an ordinary subgroup closed under ambient conjugation. For an intersection, the subgroup part is reused from the tracer theorem; only conjugation closure is proved componentwise in H and K.

**AI system.** N004 first committed with the layered proof. A fresh-session body-deletion probe rolled back at the final normality goal, and replaying the layered proof committed again. This makes the dependency boundary explicit instead of hiding normality inside a larger script.


```litex
thm normal_subgroup_intersection_closed:
    ? forall G nonempty_set, group &group::Group<G>, H, K power_set(G):
        $is_normal_subgroup(G, group, H)
        $is_normal_subgroup(G, group, K)
        =>:
            $is_normal_subgroup(G, group, {x G: x $in H and x $in K})
    by thm subgroup::subgroup_intersection_closed(G, group, H, K) => $subgroup::is_subgroup(G, group, {x G: x $in H and x $in K})
    claim:
        ? forall g, h G:
            h $in {x G: x $in H and x $in K}
            =>:
                group.mul(group.mul(g, h), group.inv(g)) $in {x G: x $in H and x $in K}
        group.mul(group.mul(g, h), group.inv(g)) $in H
        group.mul(group.mul(g, h), group.inv(g)) $in K
    by def $is_normal_subgroup(G, group, {x G: x $in H and x $in K})
```

Structured evidence:


```json
{
  "block": "N004",
  "status": "materialized",
  "attempts": [
    {
      "attempt_id": "N004-A1",
      "result": "accepted_final",
      "verifier_evidence": "persistent session block N004-A1 returned Committed/Success; after the deletion probe rolled back, fresh-session block N004-A1-REPLAY again returned ok: true, Committed, DefThmStmt, and verify_process: Success"
    },
    {
      "attempt_id": "N004-A2",
      "result": "rejected",
      "verifier_evidence": "fresh persistent session block N004-A2 returned TryStmt execution kind: RolledBack; failed_goal was the final is_normal_subgroup conclusion; verify_process reported Error: cannot prove then-clause"
    }
  ]
}
```

### 17 / quotient groups: Package the normal-subgroup quotient and its projection

**Mathematics.** For a normal subgroup H, multiplication and inverse on left cosets do not depend on the chosen representatives. Those operations satisfy the group laws on G/H, and the map g ↦ gH preserves identity and multiplication.

**AI system.** QG001-QG020 were replayed from a clean prefix. The bodyless QG021 then passed well-definedness but rolled back on the exact group-homomorphism goal; the production proof committed next, and the generated source passed both strict file and complete-module gates.


```litex
thm quotient_group_mk_is_group_hom:
    ? forall G nonempty_set, group &group::Group<G>, H power_set(G):
        $normal_subgroup::is_normal_subgroup(G, group, H)
        =>:
            $group_homomorphism::is_group_hom(G, \quotient_group_nonempty<G, group, H>, group, \quotient_group<G, group, H>, \quotient_group_mk<G, group, H>)
    \quotient_group<G, group, H>.one = \quotient_group_one<G, group, H> = \quotient_group_mk<G, group, H>(group.one)
    \quotient_group_mk<G, group, H>(group.one) = \quotient_group<G, group, H>.one
    claim:
        ? forall x, y G:
            \quotient_group_mk<G, group, H>(group.mul(x, y)) = \quotient_group<G, group, H>.mul(\quotient_group_mk<G, group, H>(x), \quotient_group_mk<G, group, H>(y))
        \quotient_group<G, group, H>.mul = \quotient_group_mul<G, group, H>
        \quotient_group<G, group, H>.mul(\quotient_group_mk<G, group, H>(x), \quotient_group_mk<G, group, H>(y)) = \quotient_group_mul<G, group, H>(\quotient_group_mk<G, group, H>(x), \quotient_group_mk<G, group, H>(y))
        release thm quotient_group_mul_mk(G, group, H, x, y)
        \quotient_group_mul<G, group, H>(\quotient_group_mk<G, group, H>(x), \quotient_group_mk<G, group, H>(y)) = \quotient_group_mk<G, group, H>(group.mul(x, y))
    by def:
        ? $group_homomorphism::is_monoid_hom(G, \quotient_group_nonempty<G, group, H>, group.mul, group.one, \quotient_group<G, group, H>.mul, \quotient_group<G, group, H>.one, \quotient_group_mk<G, group, H>)
    by def:
        ? $group_homomorphism::is_group_hom(G, \quotient_group_nonempty<G, group, H>, group, \quotient_group<G, group, H>, \quotient_group_mk<G, group, H>)
```

Structured evidence:


```json
{
  "block": "QG021",
  "status": "materialized",
  "accepted_attempt": {
    "attempt_id": "QG021A2",
    "result": "accepted_clean_replay",
    "verifier_evidence": "After the uncontaminated QG001-QG020 replay and bodyless rollback QGLIVE004, the exact production proof committed with all verifier phases Success."
  },
  "liveness_probe": {
    "attempt_id": "QGLIVE004",
    "verify_well_definedness": "Success",
    "verify_process": "Error",
    "affect_environment": "NotRun",
    "execution_kind": "RolledBack",
    "failed_goal": "group_homomorphism::is_group_hom for the canonical quotient projection"
  },
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "statement_count": 164,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 18 / finite function spaces: Count functions by adjoining one input point

**Mathematics.** A function on {z} ∪ S is uniquely determined by its restriction to S and its value at z. The explicit extension map is a bijection `(S → B) × B ≃ ({z} ∪ S → B)`, so finite-set induction gives `|A → B| = |B|^|A|`.

**AI system.** FF001-FF019 were replayed from their exact journal sources by a reusable framed-session client. The bodyless FF020 rolled back on the precise cardinality-property goal, the restored proof committed, and independent strict file and full-module runs each reported 239 successful statements.


```litex
thm finite_function_space_count:
    ? forall A, B finite_set, default B:
        $finite_function_space_count_property(A, B)
    witness $is_nonempty_set(B) from default
    by induc P in A:
        ? $finite_function_space_count_property(P, B)
        ? from P = {}:
            release thm finite_function_space_count_empty(B, default)
            $finite_function_space_count_property({}, B)
            $finite_function_space_count_property(P, B)
        ? induc z, S:
            release thm finite_function_space_count_insert_step(A, B, default, z, S)


# Arithmetic foundation for orbit sizes in finite p-group actions.
```

Structured evidence:


```json
{
  "block": "FF020",
  "status": "materialized",
  "accepted_attempt": {
    "attempt_id": "FF020A2",
    "result": "accepted_clean_replay",
    "verifier_evidence": "After replaying exactly FF001-FF019 and observing the bodyless rollback, the exact production proof committed again."
  },
  "liveness_probe": {
    "frame_id": "FF020-BODYLESS",
    "result": "rejected_rolled_back",
    "verify_well_definedness": "Success",
    "execution_kind": "RolledBack",
    "failed_goal": "$finite_function_space_count_property(A, B)",
    "diagnosis": "After a clean FF001-FF019 replay, the exact final theorem header is meaningful but the cardinality property is not available without the induction proof."
  },
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "output_bytes": 281132176,
    "statement_count": 239,
    "all_statement_outcomes_success": true,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 19 / prime arithmetic: Expose exactly the Euclid lemma needed by p-group counting

**Mathematics.** The Euclidean algorithm gives Bezout coefficients for gcd. If a prime p divides ab but not a, then gcd(p,a)=1; multiplying a Bezout identity by b shows p divides b. This is the only prime-factor interface the orbit-size argument needs.

**AI system.** PA001-PA010 were replayed from exact Chapter 2/5 source slices with explicit namespace rewrites. The bodyless PA011 rolled back at `p|a or p|b`; its proof committed, PA012 supplied integer cancellation, and strict file/module runs reported 251 and 261 successful statements respectively.


```litex
thm prime_divides_product:
    ? forall p N+, a, b N:
        $prime(p)
        $group::divides(p, a * b)
        =>:
            $group::divides(p, a) or $group::divides(p, b)
    by cases:
        ? $group::divides(p, a) or $group::divides(p, b)
        case $group::divides(p, a):
            $group::divides(p, a) or $group::divides(p, b)
        case not $group::divides(p, a):
            release thm gcd_positive(p, a)
            have g N+ = gcd(p, a)
            release thm gcd_divides_left(p, a)
            release thm gcd_divides_right(p, a)
            $group::divides(g, p)
            $group::divides(g, a)
            claim:
                ? g = 1
                by contra:
                    ? g = 1
                    g != 1
                    g >= 1
                    g $in N
                    claim:
                        ? g >= 2
                        by contra:
                            ? g >= 2
                            g < 2
                            g <= 1
                            g >= 1
                            g = 1
                            impossible g != 1
                    release thm _positive_divisor_le_abs(g, p)
                    g <= abs(p) = p
                    claim:
                        ? g = p
                        by contra:
                            ? g = p
                            g != p
                            claim:
                                ? g < p
                                by contra:
                                    ? g < p
                                    g >= p
                                    g <= p
                                    g = p
                                    impossible g != p
                            g $in range(2, p)
                            claim:
                                ? p % g != 0
                                by def $prime(p)
                            obtain d from exist d Z st {p = g * d}
                            p % g = (g * d) % g = 0
                            impossible p % g != 0
                    $group::divides(p, a)
                    impossible not $group::divides(p, a)
            release thm bezout_identity_positive_first(p, a)
            obtain x, y from exist x, y Z st {gcd(p, a) = p * x + a * y}
            obtain z from exist z Z st {a * b = p * z}
            a * y * b = (a * b) * y = p * z * y
            (p * x + a * y) * b = p * x * b + a * y * b = p * x * b + p * z * y
            witness $group::divides(p, b) from x * b + z * y:
                b = 1 * b = gcd(p, a) * b = (p * x + a * y) * b = p * x * b + p * z * y = p * (x * b + z * y)
            $group::divides(p, a) or $group::divides(p, b)

```

Structured evidence:


```json
{
  "block": "PA011",
  "status": "materialized",
  "accepted_attempt": {
    "attempt_id": "PA011A2",
    "result": "accepted_clean_replay",
    "verifier_evidence": "After a clean PA001-PA010 replay and bodyless rollback, the exact transformed production theorem committed again."
  },
  "liveness_probe": {
    "frame_id": "PA011-BODYLESS",
    "result": "rejected_rolled_back",
    "verify_well_definedness": "Success",
    "execution_kind": "RolledBack",
    "failed_goal": "group::divides(p, a) or group::divides(p, b)",
    "diagnosis": "The Euclid-lemma statement is well formed after the gcd/Bezout prefix, but its disjunctive conclusion is not available when the proof body is removed."
  },
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "output_type": "strict full run",
    "output_bytes": 285100558,
    "statement_count": 251,
    "all_statement_outcomes_success": true,
    "direct_trust": 0,
    "axioms": 0,
    "trusted_object_assumptions": 0,
    "unverified_imports": []
  }
}
```

### 20 / Cauchy pipeline: Turn prime divisibility into a prime-order subgroup

**Mathematics.** Finite p-group orbit counting proves the needed fixed-point congruence. Applied to cyclic rotation on product-one tuples, it yields Cauchy's theorem: a prime dividing a finite group order produces an element, and hence a subgroup, of order p.

**AI system.** The proof is split across finite function spaces, p-group actions, cyclic tuples, restriction, rotation, fixed points, the power homomorphism, and the final Cauchy interface. Each file owns a source-order JSON journal and a replay mirror.


```litex
release thm cauchy_theorem::cauchy_prime_subgroup_exists_auto(Q, quotient_group, p)
obtain K from exist K power_set(Q) st {$subgroup::is_subgroup(Q, quotient_group, K), $is_finite_set(K), finite_set_size(K) = p}
```

Structured evidence:


```json
{
  "claim": "The ordered Cauchy files are active, mirrored under web/replay, and consumed by normalizer_quotient_has_prime_subgroup."
}
```

### 21 / quotient preimage: Factor one hard cardinality proof into coordinate files

**Mathematics.** For K ≤ N_G(H)/H, every element of its preimage has coordinates (its coset, its residual element of H). Reconstruction proves a bijection preimage(K) ≃ K × H.

**AI system.** A monolithic proof timed out after fully scalarizing tuple and cancellation steps. The successful repair moved coordinate identities, typed maps, bijection, and cardinality into separate files. QPB005A1 rolled back because a local alias did not unfold; QPB005A5 committed after explicit unfolding and a fresh file checkpoint.


```litex
try:
    thm sylow_preimage_coordinate_bijective:
        ? ... =>:
            exist coordinate_forward fn(x preimage(K)) cart(K, H)
            st {$bijective(preimage(K), cart(K, H), coordinate_forward)}
        # explicitly unfold the fixed-K forward/backward maps
        # prove left inverse, right inverse, then package the witness
```

Structured evidence:


```json
{
  "claim": "QPB005A1 RolledBack at local forward unfolding; QPB005A5 Committed. The materialized file then passed a clean file-backed replay."
}
```

### 22 / cardinality: Read the coordinate bijection as a product formula

**Mathematics.** The bijection immediately gives |preimage(K)| = |K × H| = |K||H|. This is the exact numerical bridge needed by the Sylow successor step.

**AI system.** Once the coordinate and bijection interfaces were separated, the cardinality theorem became a six-line consumer and committed on QPCARD001A1.


```litex
release thm quotient_preimage::sylow_quotient_preimage_finite(G, group, H, K)
release thm quotient_preimage_bijection::sylow_preimage_coordinate_bijective(G, group, H, K)
obtain coordinate_forward from exist result fn(x preimage(K)) cart(K, H) st {$bijective(preimage(K), cart(K, H), result)}
$is_finite_set(cart(K, H))
finite_set_size(preimage(K)) = finite_set_size(cart(K, H)) = finite_set_size(K) * finite_set_size(H)
```

Structured evidence:


```json
{
  "claim": "QPCARD001A1 committed; root and replay SHA-256 are identical; clean replay passed."
}
```

### 23 / successor: Grow p^k to p^(k+1)

**Mathematics.** Cauchy in N_G(H)/H gives a subgroup K of order p. Pulling K back gives a subgroup P with |P| = |K||H| = p·p^k = p^(k+1).

**AI system.** The mathematical step and the divisibility-predecessor arithmetic are isolated in sylow_successor.lit. Both declarations committed on their first literal try and passed clean replay.


```litex
release thm normalizer_quotient::normalizer_quotient_has_prime_subgroup(G, group, H, p, k)
obtain K from exist K ... st {finite_set_size(K) = p}
release thm quotient_preimage_cardinality::sylow_quotient_preimage_cardinality(G, group, H, K)
finite_set_size(preimage(K)) = p * p^k = p^(k + 1)
```

Structured evidence:


```json
{
  "claim": "SS001A1 and SS002A1 both committed; clean replay and byte-identical mirror checks passed."
}
```

### 24 / induction and gate: Close the induction and audit the whole cabinet

**Mathematics.** The base subgroup is {1}. For the induction step, p^(k+1) dividing |G| implies p^k divides |G|; the induction hypothesis supplies H of order p^k, and the successor theorem supplies the subgroup of order p^(k+1).

**AI system.** SY001A1 and SY002A1 committed in a persistent file-backed session. The materialized sylow.lit passed clean replay, a strict file gate, and a strict complete-repository gate; source scan found no active trust or abstract_prop.


```litex
thm p_power_subgroup_exists:
    ? forall G nonempty_set, group &group::Group<G>, p N+, n N:
        $is_finite_set(G)
        $prime(p)
        $group::divides(p^n, finite_set_size(G))
        =>:
            exist H power_set(G) st {$subgroup::is_subgroup(G, group, H), $is_finite_set(H), finite_set_size(H) = p^n}
```

Structured evidence:


```json
{
  "status": "proved_strict",
  "active_declaration": true,
  "trust": 0,
  "missing_layers": [],
  "session_probe": {
    "frame_id": "SY002A1",
    "transport_ok": true,
    "execution_kind": "Committed",
    "well_definedness": "Success",
    "failed_phase": null,
    "failed_goal": null,
    "diagnosis": "The final induction theorem committed in the persistent file-backed session after its induction predicate committed as SY001A1."
  },
  "strict_file_gate": {
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true
  },
  "strict_repository_gate": {
    "command": "target/debug/litex -strict -r scripts/ai_litex_sylow/web/replay",
    "result": "success",
    "process_exit_code": 0,
    "top_level_ok": true,
    "error": null
  },
  "materialization": {
    "status": "materialized_in_root_and_replay",
    "clean_replay": "passed",
    "runtime": "target/debug/litex",
    "sha256": "cd4d0f4d4c0ce89c3e675e4286599d71afb03bb423c7c54fe938c7efb8b74fbe",
    "trust_scan": "passed",
    "strict_file": {
      "status": "passed",
      "command": "target/debug/litex -strict -f scripts/ai_litex_sylow/web/replay/sylow.lit",
      "exit_code": 0,
      "top_level_ok": true,
      "error": null,
      "trace_bytes_approx": 530884366
    },
    "strict_repository": {
      "status": "passed",
      "command": "target/debug/litex -strict -r scripts/ai_litex_sylow/web/replay",
      "exit_code": 0,
      "top_level_ok": true,
      "target": "repository",
      "error": null,
      "trace_bytes": 531327173
    }
  }
}
```

## Verification and trust boundary

Recorded creation-time evidence:

- Clean file-backed replay of the source now archived as [`replay/sylow.lit`](replay/sylow.lit): passed on the verifier build used to create the development.
- Strict final-file gate on that build: exit 0, top-level `ok: true`, `error: null`.
- Strict complete-repository gate on that build: exit 0, top-level `ok: true`, `error: null`.
- Active-source scan for `trust` and `abstract_prop`: zero matches.
- Root `sylow.lit` and replay mirror SHA-256: `cd4d0f4d4c0ce89c3e675e4286599d71afb03bb423c7c54fe938c7efb8b74fbe`.

Current-checkout status:

- The snapshot contains documentation, Litex source, JSON evidence, and current
  `litex.config`/`.order` metadata; the former Web UI is not included.
- The last recorded current-release execution did not reproduce the
  creation-time success and stopped at the compatibility failures described
  above. The presence of the current manifest is not a replacement for that
  missing current-HEAD gate.
- No `.lit` source was rewritten to hide that verifier drift.

Established by the recorded run:

- Every configured dependency file through sylow.lit is active and available under a strict registered path
- p_power_subgroup_exists is an active theorem whose root source and replay mirror are byte-identical
- The strict final-file and complete-repository gates exit 0 with top-level ok true and error null
- No active cabinet Litex source contains trust or abstract_prop

Outside this claim:

- The Litex parser, verifier, builtin rules, inference rules, and runtime remain part of the checker boundary
- This showcase proves the first Sylow existence theorem, not the conjugacy or counting theorems usually called the second and third Sylow theorems
- The journals are workflow evidence for this development; broader claims about AI productivity require independent tasks and measurements
- No browser UI is retained; the Markdown walkthrough and JSON journals preserve the inspectable evidence

The Litex parser, verifier, builtin rules, inference rules, runtime, and exact verifier version remain the checker boundary. The recorded strict result establishes that the creation-time configured development contained no unchecked `trust`; it is not a claim that current `HEAD` accepts the source unchanged, nor that the implementation has received the maturity or audit history of Lean’s kernel.

## Source journals

- [`proof_journals/cauchy_fixed_points_journal.json`](proof_journals/cauchy_fixed_points_journal.json)
- [`proof_journals/cauchy_power_hom_journal.json`](proof_journals/cauchy_power_hom_journal.json)
- [`proof_journals/cauchy_restriction_journal.json`](proof_journals/cauchy_restriction_journal.json)
- [`proof_journals/cauchy_rotation_journal.json`](proof_journals/cauchy_rotation_journal.json)
- [`proof_journals/cauchy_theorem_journal.json`](proof_journals/cauchy_theorem_journal.json)
- [`proof_journals/cauchy_tuples_journal.json`](proof_journals/cauchy_tuples_journal.json)
- [`proof_journals/cosets_journal.json`](proof_journals/cosets_journal.json)
- [`proof_journals/cyclic_group_journal.json`](proof_journals/cyclic_group_journal.json)
- [`proof_journals/finite_function_spaces_journal.json`](proof_journals/finite_function_spaces_journal.json)
- [`proof_journals/function_inverse_journal.json`](proof_journals/function_inverse_journal.json)
- [`proof_journals/group_actions_journal.json`](proof_journals/group_actions_journal.json)
- [`proof_journals/group_homomorphism_journal.json`](proof_journals/group_homomorphism_journal.json)
- [`proof_journals/lagrange_journal.json`](proof_journals/lagrange_journal.json)
- [`proof_journals/normal_subgroup_journal.json`](proof_journals/normal_subgroup_journal.json)
- [`proof_journals/normalizer_journal.json`](proof_journals/normalizer_journal.json)
- [`proof_journals/normalizer_quotient_journal.json`](proof_journals/normalizer_quotient_journal.json)
- [`proof_journals/p_group_actions_journal.json`](proof_journals/p_group_actions_journal.json)
- [`proof_journals/prime_arithmetic_journal.json`](proof_journals/prime_arithmetic_journal.json)
- [`proof_journals/proof_journal.json`](proof_journals/proof_journal.json)
- [`proof_journals/quotient_groups_journal.json`](proof_journals/quotient_groups_journal.json)
- [`proof_journals/quotient_preimage_bijection_journal.json`](proof_journals/quotient_preimage_bijection_journal.json)
- [`proof_journals/quotient_preimage_cardinality_journal.json`](proof_journals/quotient_preimage_cardinality_journal.json)
- [`proof_journals/quotient_preimage_coordinates_journal.json`](proof_journals/quotient_preimage_coordinates_journal.json)
- [`proof_journals/quotient_preimage_journal.json`](proof_journals/quotient_preimage_journal.json)
- [`proof_journals/subgroup_maps_journal.json`](proof_journals/subgroup_maps_journal.json)
- [`proof_journals/subgroup_structure_journal.json`](proof_journals/subgroup_structure_journal.json)
- [`proof_journals/sylow_coset_action_journal.json`](proof_journals/sylow_coset_action_journal.json)
- [`proof_journals/sylow_journal.json`](proof_journals/sylow_journal.json)
- [`proof_journals/sylow_successor_journal.json`](proof_journals/sylow_successor_journal.json)
