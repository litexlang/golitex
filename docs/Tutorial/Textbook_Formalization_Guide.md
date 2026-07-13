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

This section is the core rulebook for turning textbook content into a Litex formalization plan. Ask AI to use `chap9.md` in the appendix as the model and classify new chapters in the same style.

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

## Appendix: Chapter 9 Outline Example

`chap9.md` is an outline example for Terry Tao's Analysis I Chapter 9. It shows how to split one chapter into `narrative`, `object definition`, `prop definition`, `thm`, and `example sketch` items before writing the final `.lit` files.

This appendix illustrates several important patterns:

- The sequence convention is recorded as `narrative`, because Tao's book indexes sequences from `N`, while this Litex workspace treats `a seq(R)` as a function from `N_pos` to `R`.
- Narrative notes such as the sequence convention should be written as local `sketch:` blocks when they include runnable Litex examples, so they do not pollute the chapter's global theorem environment.
- Intervals are `object definition` items, but the later Litex code should prefer existing interval notation.
- Epsilon-adherent points, adherent points, closed sets, limit points, isolated points, and bounded sets are `prop definition` items.
- Lemmas, corollaries, and the Heine-Borel theorem are all classified as `thm`.
- Examples about adherent points are classified as `example sketch`, because they are local demonstrations rather than chapter-level dependencies.

Here is the example:

```markdown
# Terry Tao's Analysis I Chapter 9 Notes

1. narrative
Sequence in Litex is a function from `N_pos` to any set. For example, `a seq(R)` means that `a` is a function from `N_pos` to `R`, and `a seq({1, 2, 3})` means that `a` is a function from `N_pos` to `{1, 2, 3}`. Tao's book uses sequences indexed by `N`.

2. object definition
Definition 9.1.1 (Intervals). Let a, b ∈ R∗ be extended real numbers. We define the closed interval [a, b] by
[a,b]:={x∈R∗ :a≤x≤b}, the half-open intervals [a, b) and (a, b] by
[a,b):={x∈R∗ :a≤x<b}; (a,b]:={x∈R∗ :a<x≤b}, and the open intervals (a, b) by
(a,b):={x∈R∗ :a<x<b}.

3. object definition
Examples 9.1.3. If a and b are real numbers (i.e., not equal to +∞ or −∞) then all of the above intervals are subsets of the real line, for instance[2,3)={x∈R:2≤x<3}. Thepositiverealaxis{x∈ R : x > 0} is the open interval (0,+∞), while the non-negative real axis {x ∈ R : x ≥ 0} is the half-open interval [0,+∞). Similarly, the negative real axis {x ∈ R : x < 0} is (−∞, 0), and the non-positive real axis{x∈R:x≤0}is(−∞,0]. Finally,thereallineRitselfistheopen interval (−∞, +∞), while the extended real line R∗ is the closed interval [−∞, +∞]. We sometimes refer to an interval in which one endpoint is infinite (either +∞ or −∞) as half-infinite intervals

4. prop definition
Definition 9.1.5 (ε-adherent points). Let X be a subset of R, let ε > 0, and let x ∈ R. We say that x is ε-adherent to X iff there exists a y ∈ X which is ε-close to x (i.e., |x − y| ≤ ε).


5. example sketch
Example 9.1.7. The point 1.1 is 0.5-adherent to the open interval (0,1), but is not 0.1-adherent to this interval

6. prop definition
Definition 9.1.8 (Adherent points). Let X be a subset of R, and let x ∈ R. We say that x is an adherent point of X iff it is ε-adherent to X foreveryε>0.

7. example sketch
Example 9.1.9. The number 1 is ε-adherent to the open interval (0, 1) for every ε > 0 (why?), and is thus an adherent point of (0,1).

8. prop definition
Definition 9.1.10 (Closure). Let X be a subset of R. The closure of X, sometimes denoted X is defined to be the set of all the adherent points of X.

9. thm
lemma Lemma 9.1.11 (Elementary properties of closures). Let X and Y be arbitrarysubsetsofR. ThenX⊆X,X∪Y =X∪Y,andX∩Y ⊆ X∩Y. IfX⊆Y,thenX⊆Y.
Proof. See Exercise 9.1.2.

10. thm
Lemma 9.1.12 (Closures of intervals). Let a < b be real numbers, and let I be any one of the four intervals (a,b), (a,b], [a,b), or [a,b]. Then the closure of I is [a, b]. Similarly, the closure of (a, ∞) or [a, ∞) is [a, ∞), while the closure of (−∞, a) or (−∞, a] is (−∞, a]. Finally, the closure of (−∞, ∞) is (−∞, ∞).

11. thm
Lemma 9.1.13. The closure of N is N. The closure of Z is Z. The closure of Q is R, and the closure of R is R. The closure of the empty set ∅ is ∅.

12. thm
Lemma9.1.14.LetXbeasubsetofR,andletx∈R. Thenxis an adherent point of X if and only if there exists a sequence (an)∞n=0, consisting entirely of elements in X, which converges to x.

13. prop definition
Definition 9.1.15. A subset E ⊆ R is said to be closed if E = E, or
in other words that E contains all of its adherent points.

14. thm
Corollary 9.1.17. Let X be a subset of R. If X is closed, and (an)∞n=0 is a convergent sequence consisting of elements in X, then limn→∞ an also lies in X. Conversely, if it is true that every convergent sequence (an)∞n=0 of elements in X has its limit in X as well, then X is necessarily closed.

15. prop definition
Definition 9.1.18 (Limit points). Let X be a subset of the real line. We say that x is a limit point (or a cluster point) of X iff it is an adherent point of X\{x}. We say that x is an isolated point of X if x ∈ X and there exists some ε > 0 such that |x − y| > ε for all y ∈ X\{x}.

16. example sketch
Example 9.1.19. Let X be the set X = (1,2) ∪ {3}. Then 3 is an adherent point of X, but it is not a limit point of X, since 3 is not adherent to X − {3} = (1, 2); instead, 3 is an isolated point of X. On the other hand, 2 is still a limit point of X, since 2 is adherent to X − {2} = X; but it is not isolated (why?).

17. thm
Lemma 9.1.21. Let I be an interval (possibly infinite), i.e., I is a set of the form (a, b), (a, b], [a, b), [a, b], (a, +∞), [a, +∞), (−∞, a), or (−∞, a], with a < b in the first four cases. Then every element of I is a limit point of I.

18. prop definition
Definition 9.1.22 (Bounded sets). A subset X of the real line is said
to be bounded if we have X ⊂ [−M,M] for some real number M > 0.

19. thm
Theorem 9.1.24 (Heine-Borel theorem for the line). Let X be a subset
of R. Then the following two statements are equivalent: (a) X is closed and bounded.
(b) Given any sequence (an)∞n=0 of real numbers which takes values in X (i.e., an ∈ X for all n), there exists a subsequence (anj )∞j=0 of the original sequence, which converges to some number L in X.
```
