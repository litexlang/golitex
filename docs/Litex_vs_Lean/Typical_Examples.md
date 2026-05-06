# Typical example: “there are infinitely many primes” (Litex vs Lean)

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Litex_vs_Lean/Typical_Examples

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Litex_vs_Lean/Typical_Examples.md


## Example 1: There are infinitely many primes

Both snippets follow the same idea: build “product + 1”, take a prime divisor, then rule out divisors \(\le\) the bound.

**Fairness.** Litex `know` is not “cheating”: it is the same information Lean packages in `have` / `obtain` / `apply` / `calc` / case splits—just stated as upfront lemmas instead of interleaved tactic steps.

**Why Litex can feel lighter (one line each):**

1. **Blackboard-shaped syntax** — `forall`, `exist`, `claim`, `by cases`, and `%` read like ordinary math, not a tactic script driving a hidden proof state.
2. **Fewer opaque names** — you avoid ecosystem-specific incantations such as `addarith`, `extra`, or `numbers at …` just to keep the engine happy.
3. **One visible spine** — the main finish lives in a single `claim` with a short case split, instead of bullets, `match`, and nested subgoals scattered through the script.
4. **Same lemma burden** — both styles still need factorial/divisibility facts; Litex just separates “lemma block” (`know`) from “argument block” (`claim`), like a paper proof outline.
5. **Honest trade-off** — conciseness here leans on facts pushed into `know` / builtins; a fully explicit Litex file would still prove those lemmas elsewhere, as Lean would if you expanded every tactic.

---

## Code

Core proof structure (Litex `claim` … `witness` vs Lean `example … by`):

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top">
      <code>claim forall! a N_pos: 2 &lt;= a =&gt; exist k N_pos st {k &gt; a, $prime(k)}:</code><br>
      <code>&nbsp;&nbsp;2 &lt;= a &lt;= product(1, a, 'N_pos(x){x}) &lt;= product(1, a, 'N_pos(x){x}) + 1</code><br>
      <code>&nbsp;&nbsp;have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k</code><br>
      <code>&nbsp;&nbsp;by cases k &gt; a:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;case k &lt;= a:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;product(1, a, 'N_pos(x){x}) % k = 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;(product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;case k &gt; a:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;do_nothing</code><br>
      <code>&nbsp;&nbsp;witness exist k N_pos st {k &gt; a, $prime(k)} from k</code><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5; vertical-align: top">
      <code>example (N : ℕ) : ∃ p ≥ N, Prime p := by</code><br>
      <code>&nbsp;&nbsp;have hN0 : 0 &lt; N ! := by apply factorial_pos</code><br>
      <code>&nbsp;&nbsp;have hN2 : 2 ≤ N ! + 1 := by addarith [hN0]</code><br>
      <code>&nbsp;&nbsp;-- `N! + 1` has a prime factor, `p`</code><br>
      <code>&nbsp;&nbsp;obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, Prime p ∧ p ∣ N ! + 1 := exists_prime_factor hN2</code><br>
      <code>&nbsp;&nbsp;have hp2 : 2 ≤ p</code><br>
      <code>&nbsp;&nbsp;· obtain ⟨hp', hp''⟩ := hp</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;apply hp'</code><br>
      <code>&nbsp;&nbsp;obtain ⟨k, hk⟩ := hpN</code><br>
      <code>&nbsp;&nbsp;match k with</code><br>
      <code>&nbsp;&nbsp;| 0 =&gt; -- if `k` is zero, contradiction</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have k_contra :=</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;calc 0 &lt; N ! + 1 := by extra</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_ = p * 0 := hk</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_ = 0 := by ring</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;numbers at k_contra</code><br>
      <code>&nbsp;&nbsp;| l + 1 =&gt; -- so `k = l + 1` for some `l`</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;-- the key fact: `p` is not a factor of `N!`</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have key : ¬ p ∣ (N !)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· apply Nat.not_dvd_of_exists_lt_and_lt (N !)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;use l</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· have :=</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;calc p * l + p = p * (l + 1) := by ring</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_ = N ! + 1 := by rw [hk]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_ &lt; N ! + p := by addarith [hp2]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;addarith [this]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· calc N ! &lt; N ! + 1 := by extra</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_ = p * (l + 1) := by rw [hk]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;-- so `p` is a prime number greater than or equal to `N`, as we sought</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;use p</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· obtain h_le | h_gt : p ≤ N ∨ N &lt; p := le_or_lt p N</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· have : p ∣ (N !)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· apply dvd_factorial</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· extra</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· addarith [h_le]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;contradiction</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;· addarith [h_gt]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· apply hp</code><br>
    </td>
  </tr>
</table>

### Full runnable Litex (with `know` lemmas and prelude)


```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

# can be verified by induction
know:
    forall a, k N_pos:
        k <= a
        =>:
            product(1, a, 'N_pos(x){x}) % k = 0

    forall a N_pos:
        2 <= a
        =>:
            exist k N_pos st {$prime(k), a % k = 0}

    forall a N_pos:
        a <= product(1, a, 'N_pos(x){x})

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k

```
