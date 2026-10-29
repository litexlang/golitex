# Writing the Litex prompt for an agent

How to hand a Litex task to a coding agent so that it is cheap, does not thrash,
and actually understands the language. The companion artifact is
[Litex Agent Primer](Litex_Agent_Primer.md); the project skill
`.agents/skills/litex-formalizer/` bundles the same material.

This page is about the *context* you give the agent. It is not about the
mathematics, and it does not replace the [Manual](Manual.md) or the
[Learner Cheatsheet](Litex_Learner_Cheatsheet.md) for a human reader.

## The short answer

Three layers, in this order:

| Layer | Content | Size | Where it goes |
| --- | --- | --- | --- |
| Task prompt | the exact goal, the output file, the check command, the working style | 10–15 lines | the prompt |
| Primer | grammar, moves, inference rules, one accepted example per construct, two rejected→fixed turns | ~150 lines, ≈1.3k tokens | a file read once, or the bundled skill |
| Reference | `Manual.md`, `Learn_Litex.md`, `docs/` | 2.5 MB | present, cited as fallback only |

Do not paste the manual. A ~150-line primer replaces it for authoring tasks.

## Why size dominates the bill

Agent cost grows roughly as

```
tokens ≈ (prompt + accumulated context) × turns
```

because the whole context is re-read on every turn. A 600k-token documentation
context does not cost 600k tokens; it costs 600k tokens per turn. A failed
checker run costs another whole turn. So there are only two levers: shrink the
context, and reduce the number of turns. Both are bought by the agent *knowing
the moves*, not by explaining the language at length.

## Layout

```text
task/
├── problem.md     the statement, nothing else
├── TASK.md        the exact declaration to produce + the rules below
├── PRIMER.md      copy of the primer (or the litex-formalizer skill)
├── docs/          optional; fallback only
└── check          ./check solution.lit  ->  litex -lang en -strict -f
```

## The task prompt

Ten to fifteen lines is enough. What it must contain:

```text
Read problem.md and PRIMER.md, then do TASK.md.

Rules:
- Work only inside this directory.
- Do not change the statement lines in TASK.md.
- `./check solution.lit` is the only permitted outside command.
- Write one fact, run the check, then add the next fact. Never rewrite an
  accepted line.
- Start from PRIMER.md; use docs/ only if the primer lacks a construct.
- Success: `./check solution.lit` exits 0 and prints `"errors": []`.
- When it passes, reply DONE.
```

Two of those lines are load-bearing. `Do not change the statement lines` stops the
agent from proving a weaker theorem that happens to check. `Write one fact, run
the check` stops it from writing thirty lines and paying for one large failed
batch; Litex checks statements in order, so a small step is a small repair.

## What belongs in the primer

In this order, one block per job:

1. **Execution model.** One fact per line, checked in order; accepted lines stay
   usable; a rejected line reports `why_failed`; fix forward, never rewrite.
2. **Declarations.** `have`, `have fn` with the domain conditions after `:`,
   `prop` as a condition list, `cart(R, R)` with `p(1)`, `p(2)`.
3. **Theorem shape.** `thm name:` / `? forall …:` / hypotheses / `=>:` / goal,
   then indented facts. The goal is checked exactly as written.
4. **Facts.** `=`, `<=`, `| |`, `or`/`and`, `exist`, `exist!`.
5. **Moves.** `by def $P`, `release thm`, `by thm … => fact`, `witness`,
   `obtain`, `by cases`, `by contra` + `impossible`.
6. **What the checker infers.** `a + k = b + k` publishes `a = b`; `a * k = b * k`
   publishes `a = b` when `k != 0`; the same for division; chains substitute;
   `sqrt(x^2) = x` is accepted for `x >= 0`. Everything else needs its own line.
7. **Rewriting rules that shorten proofs.** Collapse an affine combination in one
   line, `(1 - t) * a + t * b = a + t * (b - a)`; use a difference bridge
   (`x - a = t * (b - a)` plus a sign fact) to reach `x > a`.
8. **Unique existence in full.** `exist!` written directly on a `thm` with a
   witness and a `claim` for uniqueness.
9. **Two rejected → `why_failed` → fixed turns.** The most valuable block: it
   turns an error into a one-line repair instead of a rewrite.
10. **Working style.** One fact per line, check after each fact, fix forward.

Leave out: history, philosophy, long prose, the full manual, and any example that
is not on the path of the task.

## Using the bundled skill

The repository ships the primer as a project skill:

```text
.agents/skills/litex-formalizer/
├── SKILL.md          instructions, working rules, what to report back
├── primer.md         the same text as docs/Litex_Agent_Primer.md
└── task-template.md  the task layout and the prompt text
```

Pi advertises a skill by name and description and loads `SKILL.md` only when the
task matches, so the primer costs nothing until a Litex task arrives. Project
skills are discovered from the working directory up to the repository root only
when project-local files are trusted: run `pi -a`, or pass
`--skill .agents/skills/litex-formalizer` explicitly. Without either, the skill
is not advertised (verified by inspecting the system prompt).

## Incremental checking is the biggest single lever

A Litex file check (`litex -f`) is not incremental: it re-parses and re-checks
the whole file and echoes every declaration. Measured on a 155-line artifact,
one successful check emits **9.4 KB** (97% of it the echoed declarations) and
takes about **1 s**. A live session (`litex -session`, driven by the `./step`
helper that ships with the skill) emits **about 0.5 KB per statement** and takes
**2–3 ms**, because accepted statements stay in the environment.

That difference multiplies: 80 checks against a whole file put roughly 750 KB of
echoed declarations into the conversation, and the model re-reads that context on
every later turn. The incremental loop puts in roughly 40 KB.

So the prompt should:

* name `./step` as the default checker and `./check solution.lit` as the final
  whole-file gate;
* say "append, then step; never re-check the whole file after every line";
* say "if `./step` prints `RESYNC`, you rewrote earlier lines and the whole file
  was re-checked", so the agent prefers appending;
* allow a few independent statements per step, since the report names the first
  failing statement.

## Ten rules

1. **Pin the goal verbatim.** Name the declaration; say it must not change; check
   the produced goal text afterwards. Otherwise "passes" and "proves the stated
   thing" diverge.
2. **Name one success command and one success token.** `./check solution.lit` and
   `"errors": []`.
3. **One fact per line, and say so.** Litex is line-by-line; prose is not a proof.
4. **Teach the loop, not only the syntax.** A rejected line plus `why_failed` plus
   the smallest fix is worth more than three more grammar rows.
5. **State the inference boundary.** Every language has a surprising one. In Litex
   it is cancellation and chains versus expansion and factoring.
6. **One accepted example per construct the task actually needs.** Not a tour.
7. **Add failure modes you observed, not ones you imagine.** Two real ones that
   matter: a `prop` body cannot hold an `exist` claim (parse error), and `sqrt`
   needs its domain condition in the goal.
8. **Prefer lines that shorten proofs.** The expensive tasks are usually not
   mathematically hard; they are an agent expanding a two-line rewrite into six.
9. **Tell it to check after each fact and to fix forward.** Rewriting an accepted
   prefix wastes tokens and re-triggers failures.
10. **Keep the manual as a cited fallback, and measure fallback use.** Doc lookups
    per task went 4.3 (docs only) → 2.0 (cheat sheet) → 0.7 (tuned primer) → 0.2.
    A rising count means the primer is missing a construct.

## Keep it honest

* Verify every snippet with the real binary before adding it. A primer line that
  does not check is worse than no line.
* Per-construct work pays; prose does not. In a local benchmark of eight small
  Litex tasks, every improvement came from adding or fixing a *snippet* for the
  single most expensive construct, never from adding explanation.
* Single samples lie. Two samples of the same artifact on the same task differed
  by 2×; keep changes only when a median over at least three runs improves and
  the pass rate holds.
* Validate on a problem that was not used for tuning.

## Measured effect

Local benchmark, one model, eight small Litex tasks (cancellation, case split,
contradiction, unique existence, a coordinate function, a square root, affine
interpolation, a predicate with an existential). Tokens are medians; the
conditions were not all run on the same task subset, so compare per-task deltas,
not the medians alone.

| Context given to the agent | Pass | Median tokens per task | Failed checker runs per task | Doc lookups per task |
| --- | ---: | ---: | ---: | ---: |
| `docs/` only | 6/6 | 65,298 | 1.00 | 4.33 |
| 90-line cheat sheet | 6/6 | 32,747 | 0.33 | 2.00 |
| primer, first version | 6/6 | 32,766 | 0.50 | 2.83 |
| primer + `exist!` block | 30/30 | 34,209 | 0.40 | 2.07 |
| primer + affine/difference blocks | 19/19 | 17,659 | 0.26 | 0.68 |
| primer + `sqrt` rule | 6/6 | 20,151 | 0.00 | 0.17 |

On three real IMO geometry tasks the tuned primer cut authoring cost from
5.62M to 1.01M tokens, from 1.47M to 0.74M, and from 2.96M to 2.05M (means over
the available runs), with every artifact still passing strict checking. Check time itself is unaffected: the
primer changes what the agent writes, not how fast the checker runs.

## Anti-patterns

* Pasting the manual or a 500-line cheat sheet into the prompt.
* Prose instructions such as "then simplify"; the checker does not accept prose.
* Examples that are not on the task's path.
* An unpinned statement, which lets a weaker theorem pass.
* Writing a large file before the first check.
* Concluding from one sample, or tuning on the validation problem.
* Letting the agent re-read `docs/` after every failure instead of fixing the
  primer where it was insufficient.

## Checklist before shipping a prompt

- [ ] goal pinned verbatim, "do not change these lines" stated
- [ ] one success command and one success token named
- [ ] primer under ~200 lines, one construct per block, no tour
- [ ] at least one rejected → `why_failed` → fix example
- [ ] explicit list of what is inferred and what must be written
- [ ] every snippet verified with the release binary
- [ ] at least one failure mode taken from a real run
- [ ] measured with at least three runs per cell; pass rate and tokens reported
- [ ] validated on a problem not used for tuning
- [ ] `docs/` reachable but not the default

## For other proof assistants

The structure transfers; only the content of blocks 6–8 changes. In Lean, the
"what is inferred" block becomes what `ring`, `norm_num`, `omega` and `simp`
close and what needs `linarith` or `nlinarith`; the per-construct snippets become
`rcases`, `obtain ⟨⟩`, `∃!`, `field_simp` followed by `ring`; and the failure
modes are unknown lemma names, `nlinarith` refusing to multiply a hypothesis by a
monomial, and `positivity` not seeing a local hypothesis. Discovery there is
`#check`/`exact?` probing rather than reading a manual, so the primer should be
shorter and spend its lines on which tactic to try.
