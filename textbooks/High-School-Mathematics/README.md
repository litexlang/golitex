# High-school mathematics: runnable foundation module

The current module exports only `HighSchoolCite::foundations`, whose checked
fact records `pi > 0`. The twenty chapter files and the remaining cite package
are preserved under `../todo_textbook_chapters/` because the shared cite prefix
does not pass the current release verifier.

```text
target/release/litex -compact -runner -r scripts/high_school_book/textbook
```

This is a verified foundation skeleton, not a completed high-school textbook.
The previous module README is preserved with the quarantined chapters.
