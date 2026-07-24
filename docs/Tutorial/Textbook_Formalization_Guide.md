# How to Formalize a Textbook

Litex source code stays the same across languages, but CLI output supports
localized JSON keys and explanatory labels with `litex -lang <code> ...`.
See [CLI](https://litexlang.com/doc/cli) for the supported language codes.

## 1. Prepare the Source Material

1. Download the textbook PDF.

2. Convert the PDF into markdown.

3. Save the result chapter by chapter. Do not start by collecting all definitions and theorems from the whole book into one global list. Many textbooks introduce motivation, examples, and local vocabulary before the formal definitions and theorems. Keeping the original order makes the dependency structure easier to see during formalization.

## 2. Generate a Chapter Outline

Ask AI to read the book chapter by chapter, from front to back, and split the content into small items. Each item should preserve the source text and receive one of the following labels:

- `narrative`
- `object definition`
- `prop definition`
- `thm`
- `example sketch`

The output of this step is one markdown file per chapter. It is not Litex code yet. Its purpose is to turn a chapter into a structured worklist for later formalization.

## 3. Classification Rules

This section is the core rulebook for turning textbook content into a Litex formalization plan. Keep the labels consistent across chapters.

- `narrative`: Use this for chapter transitions, motivation, and explanatory text. In the Litex chapter file, narrative items should not become global `claim`, `prop`, `have`, or theorem interfaces. If the narrative contains a useful runnable mathematical illustration, write it as a local `sketch:` block under the explanatory comment. If it is only ordinary explanation, keep it as comments only.

- `object definition`: Use this when the book defines a mathematical object, function, set, template, or notation. If the object already corresponds to a Litex keyword or built-in object, do not define a new wrapper. Use a local `sketch:` to show the built-in object's characteristic properties. For example, intervals can correspond to `'[a, b]`, `'(a, b)`, `'(a, b]`, `'[a, b)`, `'(a,)`, `'(,a)`, and related interval forms, and their endpoint/order facts can be shown inside `sketch:`. If the object is not built in, define it with `have` or the appropriate Litex definition form. If the textbook immediately states key properties of the new object that later arguments depend on, promote those properties to `thm`; if the properties are ordinary sanity checks or examples, keep them inside `sketch:`.

- `prop definition`: Use this when the book defines a property, predicate, or relation. Some passages look like object definitions but are really prop definitions. For example, "x is an adherent point of X" is essentially a predicate. For naming, predicates without an obvious existential structure can use `is_xxx`; properties with an existential structure can use `has_xxx`.

- `thm`: Use this for lemmas, theorems, propositions, and corollaries in the book. If one textbook theorem contains several conclusions, it can be split into several smaller `thm` items during formalization. Names can follow the mathematical meaning, the source numbering, or both.

- `example sketch`: Use this for examples after definitions or theorems. A textbook often gives many examples after one definition; the first pass does not need to formalize all of them. Pick the first representative example, or the example that best tests the current definition. Litex `sketch` opens a local environment and does not pollute the outer context, so it is a good fit for local demonstrations.

Definitions must not be skipped. Even if a complete proof cannot be written immediately, record the definition and use the smallest honest placeholder during formalization. Examples may be skipped, especially if they are repetitive or do not affect the chapter dependency chain.

For simple built-in facts inside `sketch:`, prefer the direct mathematical statement over a verbose local proof wrapper. For example, write

```litex
sketch:
    forall a, b R, x '[a, b]:
        x $in R
        a <= x
        x <= b
```

instead of wrapping the same statement in a local `claim` unless the proof steps themselves are pedagogically important.

If the source book says `Proof. See Exercise ...`, then the book itself has omitted the proof. In the first pass, record the item as a `thm`, temporarily use `trust` for the proof, mark it as proof debt, and return to it in a second pass.

Every textbook has its own style. Before processing a new book, write a custom prompt describing how that book presents definitions, examples, exercises, theorem numbering, and omitted proofs. Keep the classification labels stable, but tune the prompt to the source.

## 4. Start Formalization

After the chapter outlines are ready, formalize each markdown file one at a time. Process each item with this loop:

1. First understand the mathematical idea in natural language.
2. Choose the most Litex-native formulation.
3. Write the smallest useful Litex statement or proof attempt.
4. Run the verifier and read the exact output.
5. Make the next smallest correction.
6. Record any remaining proof debt near the source item.

The goal of the first pass is not to finish every proof. The goal is to preserve the book's mathematical structure while discovering which parts are already checkable and which parts require a source-local cite package, builtin rules, infer rules, or proof engineering.

If AI gets stuck on something you know how to do, guide it. If you also do not know how to handle the issue, file an issue in `golitex`.
