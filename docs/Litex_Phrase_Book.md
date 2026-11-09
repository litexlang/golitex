# phrase_book: A Litex Mathematical Phrasebook

[Chinese](phrase_book.md)

This phrasebook helps readers who already understand the relevant mathematics express it in Litex, then combine familiar sentence patterns to write new mathematics.

The organizing principle is: **teach composable sentence patterns, and illustrate each pattern with a correspondence between mathematical language and Litex.** The main text explains how patterns combine; each pattern is illustrated by matching mathematical phrases to their code.

This document records that structure and an initial set of examples. Further entries will follow the same format.

## Find a pattern from your mathematical intention

Start with what you want to express: “take an arbitrary object,” “if ... then ...,” “there exists ...,” “define a function,” or “choose a witness.” First see the usual spelling, then learn how it combines with other patterns.

There are two learning paths, sharing the same vocabulary:

- **State mathematics:** specify the objects, conditions, and conclusion.
- **Prove mathematics:** supply the calculation, construction, case analysis, or other argument supporting the conclusion.

“Let x be a real number” serves different roles when introducing an object and when stating a universal proposition. The phrasebook explains the distinction in context instead of mechanically replacing words with keywords.

## A consistent entry format

| Content | Question answered |
| --- | --- |
| Mathematical intention | What am I trying to do? |
| Core pattern | What is the usual spelling, and where does each part go? |
| Correspondence example | Which Litex code expresses this mathematical sentence? |
| Conditions and scope | What must already hold, and where can each variable be used? |
| Composition | Which other patterns can contain this one, and how can it be extended? |

Complete examples include their required context and can run independently. Templates containing placeholders must be labeled as templates and kept separate from runnable code. Teach one recommended spelling for each meaning first, with alternative supported spellings in supplementary notes.

## Example 1: Introduce an object, then state a fact

Mathematics: Let b be the real number 2. Then b + 1 = 3.

```litex
have b R = 2
b + 1 = 3
```

| Mathematics | Litex | Role |
| --- | --- | --- |
| Let b be the real number 2 | `have b R = 2` | Introduce an object with its number set and value |
| Then b + 1 = 3 | `b + 1 = 3` | State and check a fact |

Composition: introduce an object, then write facts about it. Each accepted fact can support later statements.

## Example 2: Quantify an object, then give a condition and conclusion

Mathematics: For every real number x, if x > 0, then x is nonzero.

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

| Mathematics | Corresponding part |
| --- | --- |
| For every real number x | `forall x R:` |
| If x > 0 | `x > 0` before the arrow |
| Then x is nonzero | `x != 0` after the arrow |

Composition: `forall` gives the variable's domain, and `=>:` separates premises from conclusions. Without premises, list the conclusions directly. The variable x is local here; this statement does not introduce an object named x for use outside it.

## Example 3: Define a function, then use it

Mathematics: Define square(x) = x² for real x. Then square(3) = 9.

```litex
have fn square(x R) R = x^2
square(3) = 9
```

| Mathematics | Corresponding part |
| --- | --- |
| Define the function square | `have fn square` |
| The input x is real | `(x R)` |
| The output is real | `R` after the parameter list |
| The function value is x² | `= x^2` |
| Apply the function to 3 | `square(3)` |

Composition: the definition introduces a callable mathematical object. Its applications can appear in equations, conditions, or other definitions. A definition must be meaningful for inputs throughout its declared domain; for example, a reciprocal function must exclude zero from its inputs.

## Example 4: Define a property, then check an instance

Mathematics: Define is_above_two(t) to mean t > 2. The number 3 satisfies this property.

```litex
prop is_above_two(t R):
    t > 2
by def $is_above_two(3)
```

| Mathematics | Corresponding part |
| --- | --- |
| Define a property | `prop is_above_two(t R):` |
| Its condition is t > 2 | `t > 2` in the definition body |
| Check by definition that 3 satisfies it | `by def $is_above_two(3)` |

Composition: `prop` names a condition. The proposition `$is_above_two(3)` can appear as a premise or conclusion where this fact shape is supported. Defining a property does not prove that every object satisfies it.

## Example 5: Combine universal quantification, existence, and construction

Mathematics: For every real number x, there exists a real number y such that y = x + 1. For the proof, choose y = x + 1.

```litex
claim:
    ? forall x R:
        exist y R st {y = x + 1}
    witness exist y R st {y = x + 1} from x + 1
```

| Mathematics | Corresponding part |
| --- | --- |
| Prove a local result | `claim:` |
| The goal to prove | The complete fact following `?` |
| For every real number x | `forall x R:` |
| There exists a real y with y = x + 1 | `exist y R st {y = x + 1}` |
| Choose y = x + 1 | `witness ... from x + 1` |

This combines familiar mathematical actions: specify a variable's domain, state existence, and give a concrete construction. The existential proposition specifies what is required; `witness` supplies an object satisfying the conditions.

The witness may depend on the current x. Replacing “for every x, there is a y” with “there is a y that works for every x” changes the mathematical meaning. A completed local proof exports its goal fact; its internal variables do not become global names.

## Coverage and expansion

The phrasebook has three layers. Readers can learn common expressions first, then consult the complete language as needed.

| Layer | Content | Organization |
| --- | --- | --- |
| Core patterns | Introduction and naming, facts and conditions, quantifiers, definitions, local proofs, and common proof actions | Use the entry format above, with correspondence examples and composition links |
| Complete language index | Other constructions, structs and templates, recursion, extensionality, reuse, modules, and related features | Map public constructs to entries, including their conditions and boundaries |
| Mathematical vocabulary | Number sets, set and function operations, domain concepts, and library interfaces | Explain mathematical meanings and conditions of use while reusing familiar patterns |

The size of the core is a teaching choice, not a substitute for checking complete coverage. Maintain the full index against the current Manual's [statement dictionary](Manual.md#statement-dictionary), [fact shapes](Manual.md#factual-statements), [object dictionary](Manual.md#object-dictionary), and [module documentation](Manual.md#project-organization).

Composition must follow the actual grammar. For example, the condition bodies of existential facts and set builders cannot directly contain arbitrary universal quantification; name the condition with a concrete `prop` when needed. Explain such boundaries where readers encounter the combination, so they do not assume that all patterns can be nested arbitrarily.

Prioritize further entries on extracting witnesses, unique existence, case analysis, contradiction, induction, set and function equality, and named theorems and their use. Then complete the language index.

## Evaluating the phrasebook

The main goal is to reduce the extra effort needed to express known mathematics correctly in Litex. Evaluate it with beginners who have the required mathematical background, using unfamiliar tasks. Record time to the first correct translation, lookups, revisions, hints, and semantic errors.

Check separately whether readers understand the core patterns, can find other language constructs, and can combine learned patterns into new correct statements and proofs. Semantic correctness needs review; program acceptance alone is insufficient. Learning times and accuracy require actual experiments. The current examples do not establish learning outcomes or coverage of all mathematics.

For precise syntax, see the [Manual](Manual.md). For everyday authoring, see the [Learner Cheatsheet](Litex_Learner_Cheatsheet.md). When checking and revising code incrementally, follow the persistent Session workflow in the [Agent Guide](AgentGuide.md).
