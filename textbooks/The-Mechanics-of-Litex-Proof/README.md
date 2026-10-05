# The Mechanics of Litex Proof

A Litex textbook covering calculation, structured proofs, logic, induction,
number theory, functions, sets and relations. Each chapter contains mathematical
statements, proof ideas and executable Litex proofs. Shared supporting theorems
are proved in `citation.lit`.

## Run

From the repository root:

```sh
cargo build --release
target/release/litex -r textbooks/The-Mechanics-of-Litex-Proof
```

For strict verification:

```sh
target/release/litex -strict -r textbooks/The-Mechanics-of-Litex-Proof
```

To check the configured book prefix through an individual chapter:

```sh
target/release/litex -strict -f textbooks/The-Mechanics-of-Litex-Proof/chapter09-sets.lit
```

`litex.config` loads the preface, citation module and Chapters 0–10 in order.

## Mathematical conventions

When a concept is already provided by Litex, the book introduces its definition
and simple examples, then uses the builtin object for later proofs. Quotients
and remainders use `quot(n, d)` and `n % d` with positive divisors. For a negative
divisor, change the quotient sign and retain the nonnegative remainder. The
builtin `gcd(a, b)` requires at least one argument to be nonzero.

Pascal's triangle is defined recursively. Bezout's identity uses the proved
citation theorem. The natural-set shift examples use `power_set(N)`.

## Contents

| Chapter | Topic |
| --- | --- |
| 0 | Introduction |
| 1 | Proofs by calculation |
| 2 | Structured proofs |
| 3 | Parity and divisibility |
| 4 | Further structured proofs |
| 5 | Logic |
| 6 | Induction |
| 7 | Number theory |
| 8 | Functions |
| 9 | Sets |
| 10 | Relations |
