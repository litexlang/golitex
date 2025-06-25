## Answers to Common Questions

_Given enough eyeballs, all bugs are shallow._

_-- Linus Torvalds_

_Software is eating the world._

_-- Marc Andreessen_

Litex's growth is driven by the needs of its users. The users shape the language, not anyone else. If you have any ideas, please contact us through [zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/) or litexlang@outlook.com.

1. Why is Litex poised for success now?

Litex represents an intellectual breakthrough in formal language design. The rapidly expanding AI industry presents the perfect opportunity, as it needs tools for ensuring AI safety, enhancing reasoning, and accelerating scientific discovery. For a long time, softwares are drastically changing nearly every industry, but how people do math is still almost the same as 100 years ago. A good formal language can be that transformative force that changes the way people do math.

2. What makes Litex different from other formal languages?

Litex's greatest strength is its remarkable simplicity. While other formal languages require years of expertise to master, Litex is intuitive enough for children to learn, striking the perfect balance between power and accessibility.

3. How do I formalize concepts like uniform distribution over (0,1) or anything like that?

Think of formalization like reading a book - you need to understand the previous pages before the last one. Similarly, formalizing advanced concepts requires building up from fundamentals. For example, formalizing uniform distribution over (0,1) requires many prerequisites. The good news is that translating mathematical concepts to Litex is straightforward once you have the prerequisites in place.

4. Resources of Litex:

[Applications of Formal Reasoning in AI and Many Other Fields](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md)

[Tutorial](./doc/tutorial/tutorial.md)

[Formalization of Hilbert Geometry Axioms](./examples/comprehensive_examples/Hilbert_geometry_axioms_formalization.lix)

[Litex for Curious Lean users](./doc/litex_for_curious_lean_users/litex_for_curious_lean_users.md)

[Website](https://litexlang.org)

[Github](https://github.com/litexlang/golitex)

5. Who might benefit from Litex?

See [Applications of Formal Reasoning in AI and Many Other Fields](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md) for more details.

1. AI researchers. Researchers from OpenAI, Google, Alibaba, DeepSeek, etc are exploring the loop of model itself writes a question, itself solves, and in this way, the model itself improves itself. This is a very promising direction. They need something to tell whether the reasoning process is correct. Litex can be used to ensure the correctness of the reasoning process as long as the reasoning process is formalized in Litex. This makes Litex a very fundamental infrastructure for AI. At the same time, AI safety researchers need to ensure the safety of the output of the model, and now they are turning to formal languages for help. As models are becoming more and more powerful and dangerous, the need for formal languages is becoming more and more urgent.

2. Mathematicians. As we all know, a small piece of error in a proof can lead to a huge disaster, while somehow human beings still manage to push the frontier of math to a very high level. This is truly remarkable. That is why I am excited to see what we can do with Litex, a power tool ensuring the correctness of any piece of reasoning and saving mathematicians from the tedious work of proof checking. Mathematicians can finally work together with a stranger and the Litex kernel gives you the certificate of correctness of his/her contribution. The scale of collaboration, the scale of mathematical discovery, and the scale of mathematical knowledge are all going to be scaled up to a new level that nobody can imagine.

3. Students. Students can use Litex to learn math and formal reasoning. They can use Litex to write their own proofs and verify them. They can use Litex to learn how to write formal proofs.


6. What is the similarity and difference between Litex and Prolog?

Prolog might be the programming language that is most similar to Litex. There are still some differences between them.

Similarities:

1. Both of them uses match and substitute to derive new facts from existing facts. They both can express existence and universal quantification.

Differences:

1. Unknown facts are by default false in Prolog, while in Litex, they are by default unknown. This is a very important difference. Since what can not say a claim must be false even if nobody can prove it for the time being, we can not say a claim that is not known to be true must be false.

2. Litex is not a programming language, which is a read-only Turing Machine. Prolog is a programming language, which is a Turing complete language.

3. Prolog does not have a type system, making it hard to express set theory, which is the foundation of mathematics. This makes translation from natural language to Prolog unimaginably hard. Litex by design has a set system that is very easy to use.

4. Compared to Litex, Prolog is still too complicated and foreign to most people, partly because it is a programming language. The biggest strength of Litex is that its extremely deep insight into the nature of math and its extremely simple design to make the language as natural as possible. Just like you can use Python or Assembly to write a program and in most cases, Python is easier to use, Litex is easier to use than Prolog.

5. Technical difference: 1. exist proposition must be given a name in Litex and it is user's duty to specify which object satisfy the proposition requirement. 2. prolog might encounter dead lock when proving iff condition, and Litex avoids infinite search by setting the upper bound of searching to 2 layers. 3. In Litex, you can express forall facts without giving it a name, while Prolog forces you to do so.




