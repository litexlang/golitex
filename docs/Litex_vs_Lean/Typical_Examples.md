# Typical example: “there are infinitely many primes” (Litex vs Lean)

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

### Lean

```lean
example (N : ℕ) : ∃ p ≥ N, Prime p := by
  have hN0 : 0 < N ! := by apply factorial_pos
  have hN2 : 2 ≤ N ! + 1 := by addarith [hN0]
  -- `N! + 1` has a prime factor, `p`
  obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, Prime p ∧ p ∣ N ! + 1 := exists_prime_factor hN2
  have hp2 : 2 ≤ p
  · obtain ⟨hp', hp''⟩ := hp
    apply hp'
  obtain ⟨k, hk⟩ := hpN
  match k with
  | 0 => -- if `k` is zero, contradiction
    have k_contra :=
    calc 0 < N ! + 1 := by extra
      _ = p * 0 := hk
      _ = 0 := by ring
    numbers at k_contra
  | l + 1 => -- so `k = l + 1` for some `l`
    -- the key fact: `p` is not a factor of `N!`
    have key : ¬ p ∣ (N !)
    · apply Nat.not_dvd_of_exists_lt_and_lt (N !)
      use l
      constructor
      · have :=
        calc p * l + p = p * (l + 1) := by ring
          _ = N ! + 1 := by rw [hk]
          _ < N ! + p := by addarith [hp2]
        addarith [this]
      · calc N ! < N ! + 1 := by extra
          _ = p * (l + 1) := by rw [hk]
    -- so `p` is a prime number greater than or equal to `N`, as we sought
    use p
    constructor
    · obtain h_le | h_gt : p ≤ N ∨ N < p := le_or_lt p N
      · have : p ∣ (N !)
        · apply dvd_factorial
          · extra
          · addarith [h_le]
        contradiction
      · addarith [h_gt]
    · apply hp
```

### Litex

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

# prove forall positive integer a, there exists a prime number k larger than a
# Step1: There exists a prime number k that divides factorial(a) + 1
# Step2: Therefore, k must be greater than a. Prove case by case: k <= a or k > a
    # By Step1, factorial(a) + 1 is divisible by k
    # However, (factorial(a) + 1) % k = 1 != 0
    # So case k <= a is impossible
# Step3: Therefore, there exists a prime number k that is greater than a
claim:
    prove:
        forall a N_pos:
            2 <= a
            =>:
                exist k N_pos st {k > a, $prime(k)}
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases:
        prove:
            k > a
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```