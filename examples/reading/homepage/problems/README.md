# Passing and failing examples

Four independent pairs show an intended failure and a strict checked
correction. They are excluded from the main `litex.config`: one failed exercise
must not stop or invalidate the normal mathematical collection.

| Exercise | Problem | Correction |
| --- | --- | --- |
| [Undefined name](undefined-name.lit) | `problem_score` is used before declaration. | [Declare it first](undefined-name-fixed.lit). |
| [Zero divisor](zero-divisor.lit) | `1 / 0 = 1 / 0` is not meaningful; reflexivity cannot bypass the domain. | [Use a nonzero divisor](zero-divisor-fixed.lit). |
| [Square-root domain](sqrt-domain.lit) | The real `sqrt` does not accept `-1`. | [Use a nonnegative input](sqrt-domain-fixed.lit). |
| [Missing premise](missing-premise.lit) | A mortality implication alone does not prove that Socrates is human. | [Supply both premises](missing-premise-fixed.lit). |

The Socrates exercise declares two abstract predicate names, then checks a
conditional statement. It adds no axiom or trust. `people` is the nonempty
universe of discussion, not a claim that all its members are human. Failure to
prove the final statement is not proof of its negation. The corrected result's
actual citations include `$is_human(socrates)` and the universal mortality rule,
as well as the object's membership in the universe.

Generate the complete website, including the **Passes / Does not pass** menu categories:

```sh
python3 examples/reading/homepage/export_gallery.py <output-directory>
```

`--reuse-main` keeps an already verified main export and rebuilds only the eight
exercise pages. Each command checks the expected export status: broken files
must return exit 1 and reading `run_result: failure`; corrections must return
exit 0 and `success`. The output `problem-examples-verification.json` records
the results. Serve the output directory over HTTP to navigate among the pages.

`cases.json` records the source, mathematical issue, correction and expected
status. `reading-titles.json` supplies authored Chinese/English names. Source
comments explain the issue without claiming that error-underlining or an
inline code editor already exists.
