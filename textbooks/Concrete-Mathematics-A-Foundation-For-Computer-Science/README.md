# Concrete Mathematics in Litex

This public module currently contains the verified runnable prefix of
*Concrete Mathematics: A Foundation for Computer Science*.

## Published prefix

- Chapter 1, **Recurrent Problems**: Tower of Hanoi, line-region recurrences,
  triangular sums, Josephus recurrences, and binary/radix recurrence
  interfaces.

Run the complete published prefix with:

```text
target/release/litex -graph -r scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science/textbook
```

The current release runner checks Chapter 1 and the one-chapter dependency
closure with exit code 0 and top-level `ok:true`.

## Trust boundary

Chapter 1 inherits 29 executable trust markers from the former development
module. They are localized around the bent-line closed form, Josephus and
binary/radix recurrence interfaces, and cold-replay performance fallbacks.
This promotion adds no trust and is a runnable-publication claim, not a
trust-free-completeness claim. The exact boundaries and earlier checked
session experiments remain documented in `../todo.md` and `../experiments/`.

Chapters 2--6 remain quarantined under `../todo_textbook_chapters/` until each
chapter and its source-order dependency prefix pass the current release gates.
