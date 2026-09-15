# Locked premise: name is identity

Status: **locked** (new_pipeline)

Canonical design note for symbol identity, binder discipline, IR keys, and
exact IR indexing. Do not reintroduce occurrence ids or shadowing without an
explicit redesign.

Fact **verify** has no exact-IR cite path; `fact_ir_to_id` is for
store / merge dedup. Object WD reuses `VerifyObjWellDefinedResult::ByKnown`.

Related owners:

| Area | Path |
|------|------|
| Parse occupy / no-shadow | `parse/`, `runtime::ParseScope` / `AtomicName` |
| AST atoms | `ast/obj.rs` `IdentifierObj { name: AtomicName }` |
| Binder params | `ast/obj.rs` `Identifier` (plain name only) |
| IR spelling | `display_and_ir/` (`ir()` = surface name; no `#id#`) |
| Fact store / IR index | `exec_env/known_fact_memory.rs` |
| Obj WD ByKnown | `execute_fact_stmt/verify_well_defined/verify_obj/` |
| WD memory | `exec_env/exec_env.rs` `WellDefinedObjectMemory` |
| Def atoms in ExecEnv | `DefinitionMemory.identifiers: HashMap<PlainName, …>` |

---

## Premise

At any time, a surface name denotes **one** symbol identity for the whole
session:

- Plain `y` is always that same `y`.
- Qualified atoms use **indices**: `WithMod { file_id, name }` and
  `WithModAndExport { mod_id, file_id, name }` (not surface import aliases).
  Same physical import under local alias `T` vs global `G` shares one `mod_id`.
- Reusing the letter after a binder scope ends is **letter reuse**, like on
  paper: stored AST may still contain binder spelling `y`, and a later
  `have y` is the same name identity, not a second binding instance.

This is the mathematical / paper convention Litex chooses for new_pipeline,
not an accident of the current implementation.

---

## The “identifier conflict” problem (why ids were removed)

### Real conflict (must stay forbidden)

If an inner binder could shadow an outer one, or nest the same name
(`{x: … {x: …}}`), then the surface spelling `x` would be ambiguous:

- IR keyed only by name would **unsoundly** identify different binders.
- Occurrence ids would be needed again to tell them apart.

So the language forbids those forms. Parse `occupy` + no same-name nesting are
the soundness fence, not `IdentifierId`.

### False conflict / false miss (what ids caused)

When each binder occurrence allocated a fresh `IdentifierId` and IR embedded
`#id#name`:

```text
trust:  forall x R: $p(x)     // IR … #1#x …
prove:  forall x R: $p(x)     // IR … #2#x …  ≠ cache key
```

Same mathematics, same spelling, **exact IR-key miss**. That is not a
mathematical distinction; it is an implementation artifact. Under name-is-
identity it is wrong.

Therefore:

- **`IdentifierId` was removed** from new_pipeline AST and id allocation.
- Atom IR is the surface name (`x`, `Mod::x`, or `Mod::Export::x`).
- Exact `FactIR` may index **every closed `Fact` shape**, including
  `forall`, because same spelling ⇒ same identity (store / merge).

### What still needs a separate id

| Id | Role |
|----|------|
| `FactId` | Proof citation / store handle |
| `WellDefinednessId` | WD proof citation (obj WD ByKnown cites this) |
| `AtomicName` / `IdentifierObj` | Module qualification (≤3 segments), not occurrence |

---

## Hard rules that make name-is-identity sound

1. **No shadowing.** An inner scope must not occupy a name still visible
   outside (`occupy` only).
2. **No same-name nesting.** Forms such as `{x R: … {x R: …}}` are forever
   forbidden; nested binders must use different names.
3. At most one **live** binding of a given `AtomicName` exists.
4. Cache / known-fact keys may treat IR spellings that use the same name as
   the same symbol. Sequential `forall x` / `{x R: …}` with the same binder
   spelling are intended to share identity for lookup.

If you weaken (1) or (2), you must redesign identity (ids, alpha, or both)
before trusting name-keyed IR again.

---

## What this is not

- **Not alpha-equivalence.** `forall x R: $p(x)` and `forall a R: $p(a)` are
  different `FactIR` keys unless a separate alpha pass exists.
  Likewise `$p({x R: x > 0})` and `$p({y R: y > 0})` are **different**
  exact-cache keys today (even though they are set-equal in math).
- **Not** “global string replace by name.” Instantiate / substitute by binder
  structure only.
- **Not** a license to index binder-internal **open scraps** as ambient facts.
  Prefer full closed-fact IR for store / merge keys.
- Export of open terms that mention a local name still needs claim/export
  discipline; that is orthogonal to this premise.

---

## Capture hazard: free letter reuse vs binder spelling in stored AST

Exact FactIR / ObjIR keys do **not** identify alpha-variants. The dangerous mistake is
elsewhere: later known-* / alpha / “rename binder to match” / global
replace-by-name.

Concrete trap:

```text
trust:  $p({x R: x > 0})     // closed fact; binder spelling x in AST
have x R                     // letter reuse: free x is now live
prove:  $p({y R: y > 0})
```

What must hold:

1. **Exact IR key:** goal IR uses `y`, known IR uses `x` ⇒ **no** key hit.
   That miss is intentional under “no alpha in IR keys”.
2. **Do not** “fix” the miss by renaming known `{x …}` ↔ goal `{y …}`
   without a real binder-aware alpha that respects capture. After `have x`,
   free `x` is live: renaming the goal binder `y` to `x` (or walking into
   the known set-builder and treating binder `x` as that free `x`) is
   capture / confusion.
3. **Do not** globally substitute free `x` into every AST node whose name
   string is `x`, including under `{x R: …}` / `forall x` binders in
   *already stored* facts. Stored binder spelling and later free `x` share
   the letter under name-is-identity, but binder **positions** still bind;
   only structural instantiate/substitute is allowed.
4. If a future alpha or set-equality rule proves
   `{x R: x > 0} = {y R: y > 0}`, that rule owns capture-avoidance; it must
   not be smuggled into exact `FactIR` keys.

So the user’s worry is real for **matching beyond exact IR**, not for
today’s cite-by-identical-`FactIR` path. Record it here so alpha / known-*
work does not quietly break soundness.

---

## Beyond cache: atomic / known-* matching layers

Name-is-identity answers “which free letter is which.” It does **not** by
itself answer “when are two binder-carrying objects the same?” Atomic-fact
search must keep these layers separate.

### Layer A — Parse fence (already locked)

While free `x` is live, a new binder must not occupy `x`. So a *new* term
cannot mix free `x` with binder `x`. The leftover risk is only **stored**
closed AST that still spells binder `x` after later letter reuse
(`have x`).

### Layer B — Exact `ObjIR` / `FactIR` (IR indexes, known-atomic keys, equality graph keys)

Same spelling ⇒ same key; different binder letters ⇒ different keys.

```text
known:  $p({x R: x > 0})
goal:   $p({y R: y > 0})   // Layer B: miss (not a bug)
```

`known_atomic` argument matching that uses equality classes still compares
**exact** `ObjIR` members of classes. It must not silently alpha-rename
set-builder / forall binders to force a key hit.

### Layer C — Structural instantiate / substitute

`forall` / `exist` / prop instantiation walks binder structure. It never
does global “replace every `x` string in the session.” When applying a
stored fact that contains binder spelling `x` while free `x` is live, the
binder region stays binder-scoped.

### Layer D — Dedicated alpha / set-equality (optional, later slot)

Mathematical sameness of `{x R: P}` and `{y R: P}` (and similar) is a
**separate** rule or known-equality edge, with capture-avoidance:

- After `have x`, you may still prove `{x R: x > 0} = {y R: y > 0}` only
  via a capture-safe alpha/set rule (or user-stated equality), **not** by
  pretending Layer B keys are equal.
- Then Layer B congruence: from `A = B` and `$p(A)` conclude `$p(B)`
  through the existing equality / known-atomic-with-equality-class path.

### How to “整” the user’s example

```text
trust:  $p({x R: x > 0})
have x R
prove:  $p({y R: y > 0})
```

Intended sound pipeline (when Layer D exists):

1. Layer B: no exact hit on `$p({y…})`.
2. Layer D (or trust/claim): prove `{x R: x > 0} = {y R: y > 0}`
   capture-safely (free `x` must not be confused with binder `x`).
3. Congruence / known-atomic-with-eq-class: from `$p(A)` and `A = B` get
   `$p(B)`.

Until Layer D exists: exact miss is **correct**; do not paper over it inside
exact-IR cite or naive known-atomic string match.

### Non-goals for Layer B

- Do not put alpha into `fact_ir_to_id` / `ObjIR` keys **by silently
  renaming surface strings**.
- Do not reintroduce occurrence ids just to make Layer B look like alpha.
- Do not “normalize all binders to a canonical *speakable* letter” in IR
  without a binder calculus (that would re-create the trap after `have x`).

---

## Design proposal: alpha-normal keys for binder-carrying objects

Goal: making `{x R: x > 0}` and `{y R: y > 0}` (and analogous anon-fn /
fn-set binders) compare equal for Layer B **without** capture bugs after
later `have x`, and without undoing name-is-identity for **free** letters.

### What “auto alpha at new” should mean

User intent: when a binder-carrying **object** is created (set builder,
anonymous function, and likely fn-set / similar), alpha is already done so
matching never depends on the binder letter the user typed.

Two mechanisms that look similar but are not:

| Mechanism | AST (display / parse) | `ObjIR` / cache key | Solves `{x}` vs `{y}` | Survives later `have x` |
|-----------|----------------------|---------------------|------------------------|-------------------------|
| Freshen binder to a new **surface** letter at construct | mutated spelling | still name strings | only if both freshen to same letter (bad) | **no** — stored letter can be reused |
| Freshen to **unspeakable** binder id at construct | needs parallel display name | id in key | yes | yes, but reintroduces binder ids |
| **Locally nameless / De Bruijn in `ir()` only** | keep user spelling | bound slots = indices; free = names | yes | yes — keys never mention binder letters |

Recommendation: **locally nameless `ObjIR` (and the same for binder-carrying
subtrees inside `FactIR`)**, computed at `ir()` time — functionally “alpha
done when the object exists as a key,” without rewriting user AST.

Construct-time mutation is optional sugar; the **source of truth for
sameness** must be the nameless key, not a renamed speakable letter.

### Locally nameless contract (proposed)

1. **Free** occurrences in IR stay surface names (`x`, `Mod::x`, `Mod::Export::x`) — name is
   identity unchanged.
2. **Bound** occurrences under a binder-carrying object are emitted as
   De Bruijn indices (or equivalent nameless slots), never as the binder’s
   surface letter.
3. Binder **arity / order / type annotations** that matter for meaning stay
   in the key; the binder *letter* does not.
4. `display_string` keeps today’s user-facing spelling (from AST names).
5. Exact IR indexes / known-atomic / equality-class keys use this `ir()`.

Sketch:

```text
AST:  {x R: x > 0}     display: {x R: x > 0}
IR:   {□ R: #0 > 0}    (bound x → index 0)

AST:  {y R: y > 0}     display: {y R: y > 0}
IR:   {□ R: #0 > 0}    identical key

AST:  {y R: y > x}     with free x
IR:   {□ R: #0 > x}    free x remains the name
```

After `trust $p({x R: x > 0})` then `have x R` then prove `$p({y R: y > 0})`:
Layer B hits — keys equal; no capture, because the key has no binder letter
`x` to confuse with free `x`.

### Scope (objects first; facts follow)

Minimum object family (user examples):

- `SetBuilder`
- `AnonymousFn` (and applied anon heads if any)
- Closely related: `FnSet` / set-bound parameter blobs that bind names

Same nameless rule should later apply to binder-carrying **facts**
(`forall` / `exist` / …) so `FactIR` indexes get the same 一劳永逸
property; can stage after objects if needed.

### Construct-time vs `ir()`-time

- **`ir()`-time nameless (preferred):** no AST rewrite; parse/display stable;
  one canonical key function; harder to “forget” to alpha on some path.
- **Construct-time freshen:** only useful if something other than `ir()`
  compares raw binder names; if all sameness goes through `ir()`, it is
  redundant. If construct-time writes unspeakable ids into AST, you have
  reinvented `IdentifierId` for binders and must teach every walk to skip
  them for display.

### Discipline that remains

- Layer C still structural (instantiate by binder tree).
- Parse fence unchanged (no shadow / no nested same speakable binder).
- Do not global-replace free `x` into nameless bodies by string.
- Equality graph merges objects by nameless `ObjIR` once this ships.

### Non-goals of this proposal

- Not alpha for **free** renaming (`f(x)` vs `f(a)` stay different).
- Not silently changing what the user sees in error messages / display.
- Not putting speakable freshened letters into IR as a fake De Bruijn.

### Open decisions (need user lock before implement)

1. Nameless encoding spelling in `ObjIR` strings (e.g. `#0` vs reserved
   `__0` — see below) must not collide with user tokens — pick an
   internal-only form and document it in `display_and_ir/README.md`
   (exception to “IR = surface” **only** for bound slots).
2. Stage: objects-only first vs objects+quantified facts together.
3. Whether legacy “IR equals surface” wording is formally relaxed for
   binder carriers only.

### Variant: reserved binder names in **AST** via `alpha_normalize` (implemented)

Operation name: **`alpha_normalize`**.

When constructing binder-carrying objects (`SetBuilder`, `FnSet`,
`AnonymousFn`), `new_set_builder` / `new_fn_set` / `new_anonymous_fn` rewrite
AST binders to reserved generated names; originals stay **display-only**.
Matching / IR indexes use the normalized spelling.

**Namespace split (locked):**

| Prefix / form | Owner |
|---------------|--------|
| `__…` | **Lean / codegen only** (e.g. `__fact*`, `__arg*`). Not Litex binder identity. |
| `□0`, `□1`, … | **Litex** binder identity after `alpha_normalize` (U+25A1 WHITE SQUARE + decimal index) |

User atom names stay ASCII letter/`_` style; `□` is not a valid user atom start
in new_pipeline name rules, so users cannot introduce free `□0`. Internal AST
may still store `□N` as `Identifier.name`.

Target shape:

```text
user wrote:     {x R: x $in {y R: y > 0}}
surface:         {x R: x $in {y R: y > 0}}   // display
alpha / ir:      {□0 R: □0 $in {□1 R: □1 > 0}} // ops / IR keys
```

`SetBuilder` / `FnSet` / `AnonymousFn` store both: `surface` (user letters) and
`alpha` (`□N`). `Identifier` stays a single `name` field.

#### Why put it in AST at **new** time (user rationale — locked)

Not only for cache convenience. The motivating soundness failure:

```text
known / trust:  $p({x R: x > 0})     // if AST still literally binds "x"
have x R                              // free x is now live in the session
prove:          $p({a R: a > 0})
```

If the stored set-builder AST still uses the speakable binder letter `x`, then
after `have x` that letter is a **live free atom**. Matching / comparing /
walking the known object `{x R: x > 0}` against the goal `{a R: a > 0}` can
treat the stored binder spelling as if it were (or could interact with) that
free `x` — i.e. the stored term is already **semantically compromised** for
name-is-identity walks.

Therefore `alpha_normalize` must run when the binder-carrying object is
**constructed**, so AST identity names are already `□N`. Later `have x`
cannot poison stored binder slots. Display keeps originals only for printing.

Doing normalize only in `ir()` would leave AST spelling `x`, so AST-name
paths can still hit the bug.

#### User ban vs internal `□N` (locked preference)

| Gate | Rule |
|------|------|
| **Tokenizer / user names** | Reject `__…` (Lean reserve). User atoms cannot start with `□`. |
| **Define / AST identity** | **Allow** `□N` for binder slots after `alpha_normalize` so checks use AST/`ir` directly |

Do not free-`occupy` / `have` / `let` `□N` as session free atoms. Binder slots
are AST identity strings, not free `AtomicName` occupy entries.

#### Costs

1. Display needs original letters (display-only field).
2. `□N` are not session free atoms.
3. Structural walks only — no global string replace of `□0`.
4. `alpha_normalize` on each complete binder-obj tree at construct.
5. Quantified facts: not in phase 1.
6. `__` stays Lean-only; do not reuse `__b*` for Litex binders.

#### Nested binder-carrying objects

```text
user wrote:  {x R: x $in {y R: y > 0}}
bad:          {□0 R: □0 $in {□0 R: □0 > 0}}
good:         {□0 R: □0 $in {□1 R: □1 > 0}}
```

```text
user wrote:  {x R: {y R: y > x}}
good:         {□0 R: {□1 R: □1 > □0}}
```

```text
user wrote:  {x R: {y R: y > a}}
good:         {□0 R: {□1 R: □1 > a}}
```

**Construct rule:** one `alpha_normalize` pass per complete binder-tree root;
assign `□0`, `□1`, … uniquely (depth-first / L-to-R). Outer root re-numbers
the whole tree if an inner node was temporarily normalized while parsing.

**Cross-root alpha:**

```text
{x R: x > 0}  →  {□0 R: □0 > 0}
{y R: y > 0}  →  {□0 R: □0 > 0}
```

#### Locked plan (phase 1 — implemented)

| Item | Lock |
|------|------|
| Operation name | `alpha_normalize` |
| Binder identity spelling | `□0`, `□1`, … (U+25A1 + index) |
| `__…` | Lean / codegen only — tokenizer **returns parse error** on user source |
| Display | originals display-only; identity in AST is `□N` |
| Numbering | one counter per complete binder-carrying object tree |
| Scope (phase 1) | `SetBuilder`, `AnonymousFn` / `FnSetBody`, related obj binders |
| Out of scope (phase 1) | `forall` / `exist` |

**Why forall / exist can wait:** placeholders substituted at use; not the
nested free-obj binder problem. Do not alpha_normalize quantified facts in
phase 1.

**Still required when implementing phase 1:** structural substitute only;
`□N` never free `AtomicName` occupy; outer root re-numbers nested obj trees;
tracers for `{x:…}` vs `{y:…}` and nested builders.

---

## FactIR index contract (store / merge; no fact verify exact-IR cite)

1. On store: `fact_ir_to_id[fact.ir()] = fact.fact_id()`, and
   `facts_by_id[fact_id] = fact` (every closed `Fact` shape).
2. On merge: reuse parent FactId when child IR already exists in parent.
3. Fact **verify** does **not** cite via exact FactIR. Reuse happens
   through known-equality / known-atomic / known-forall (and future composite
   local-proof pipelines). Object WD reuses `WellDefinedObjectMemory` via ByKnown.
4. Equality-class / parameter matching / alpha belong to known-* slots, not
   to a silent IR cite.

---

## Do-not-break checklist

Before changing identity, IR, occupy, or IR indexing, check:

- [ ] No new per-occurrence id on `Identifier` / IR (`#digits#name` must not
      return).
- [ ] Parse still rejects shadowing and same-name nested binders.
- [ ] `DefinitionMemory` maps stay keyed by **`PlainName`** (unqualified local
      name; `type PlainName = String`). `Mod::Export::name` is a reference
      path, not a store key.
- [ ] Closed composite facts still enter `fact_ir_to_id` (not atomic-only).
- [ ] Binder instantiate/substitute is structural, not global rename-by-string.
- [ ] Open scraps under binders are not ambient-indexed as if free.
- [ ] Exact FactIR keys do not alpha-match set-builders / forall
      (`$p({x:…})` ↛ `$p({y:…})`). Capture-safe alpha, if any, is a later slot.
- [ ] After `have x`, never treat binder `x` inside an already-stored
      `{x:…}` / `forall x` as that free `x` via string walk.
- [ ] Obj WD ByKnown remains; do not reintroduce fact verify exact-IR cite without
      an explicit redesign.

---

## Temporary debts (do not confuse with this premise)

- Full composite well-definedness pipelines may still be stubbed
  (`FactWellDefinedProof::CompositePending`) so `trust` can store closed
  composites. That is **WD debt**, not identity debt.
- Search for `forall` / `exist` / `or` / … remains draft until wired.
