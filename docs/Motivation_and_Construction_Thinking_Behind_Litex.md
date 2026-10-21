# Motivation and Construction Thinking Behind Litex

Website: https://litexlang.com/doc/Motivation_and_Construction_Thinking_Behind_Litex

Chinese version: https://litexlang.com/doc/Litex的缘起与构建思路

Litex is built around an idea: **Write math, get formalized code: because the math already is.** From an early age, we learn that mathematics is a rigorous language: each statement needs grounds to justify its correctness. If mathematics is already a rigorous language, why couldn't mathematics itself be a formal language? Could we design one whose writing closely resembles everyday mathematics, adding just enough constraints to keep it precise?

This is an attempt to rethink the relationship between mathematics, natural language, and code from first principles—and, through that, to rethink what mathematics is and what proof means. Litex grew out of that curiosity. It aims to make mathematics itself a formal language, so that anyone who uses mathematics, from school students to AI engineers, can also use formal tools directly, without specialized training.

What follows is the thinking behind Litex's design. Its design choices build on one another, with the aim of drawing out the structures and dependencies behind everyday mathematical expression.

The first question was therefore how to find a balance between the freedom of natural language and the rigor of formal mathematics. Natural language leaves room for intuition and implicit connections. A formal language must make those connections precise enough for a machine to check.

My answer began with choosing the right mathematical foundations and just enough built-in mathematical objects and statements. A small, familiar vocabulary gives people less to learn at first sight. It also means fewer distinct concepts whose interactions the language must explain and implement. The challenge was to find a vocabulary small enough to grasp, but expressive enough to build on.

Set theory felt like a natural foundation. Sets, elements, functions, and relations already belong to the way many people understand mathematics. From there, I wanted to bring familiar mathematical notation—the symbols people routinely write in LaTeX—into the language, together with the mathematical relationships behind it. Recognizing an intersection symbol is only the beginning; the system also needs to understand how intersection relates to membership, inclusion, and equality.

With the mathematical vocabulary in place, the next question was how to write it. I chose a syntax resembling Python: indentation, visible structure, and relatively little punctuation. More importantly, I wanted users to write the mathematical statements they wanted to establish and let the kernel find the local justification for each step. The author supplies the mathematical route; the system handles the routine connections that make that route checkable.

That choice shaped the verification engine. In a typical tactic-based workflow, the author gives instructions that construct a proof, which is ultimately checked by a kernel. Litex puts the next mathematical fact at the center of the interaction: given the current context, can the system justify this statement? This is a choice about the default writing experience; other proof assistants also provide declarative interfaces and automation. Lean’s documentation explains its own elaboration and checking model.

My earliest idea for implementing this was simple: matching and substitution. Find a relevant known fact, match it against the statement being checked, and determine whether the required substitutions and conditions are valid. That idea developed into a combination of structured fact lookup, bounded recursive verification, built-in mathematical rules, and explicit statements for proof steps such as introducing witnesses or splitting into cases.

Much of the engineering lies in organizing knowledge so that the right facts can be found and used. I think of this part of Litex as a database specialized for mathematical reasoning: its storage and lookup mechanisms understand mathematical structure, scope, and the conditions under which a fact applies. The implementation is in the golitex source, and the website’s How Litex Works visualization offers another way to explore the design.

But checking a statement was only part of what I wanted. I also wanted the system to return an explanation of its verification: which facts it used, which rules connected them, and where a step could not be justified. If Litex is to help people understand mathematics, its reasoning must become something they can inspect.

Once verification produced a structured record, further possibilities emerged. The relationships between definitions and established facts could support knowledge graphs. The explanations could become part of interactive mathematics textbooks. AI agents could use the feedback to revise a failed step and continue from accepted knowledge. Building a capable mathematical agent around this interaction is one of my longer-term goals.

The same record also provides a bridge to Lean. A compiler can use both the Litex source and its verification results to generate Lean statements and proofs, following the reasoning Litex actually used. For supported translations, Lean can then independently check the generated proof. Coverage and faithful translation still need to be established route by route.

I see enormous value in that connection. It gives Litex a path into the Lean ecosystem and adds an independent check on translated proofs. It also opens the possibility of Litex serving as an accessible front end for people who want to contribute to formal mathematics through a more familiar writing style.

As a hacker, I have been exploring these questions by building something I can use, inspecting what it does, and letting each answer expose the next problem. That process continues to change how I think about mathematics, code, and proof.

I believe mathematics will become even more important in the age of AI. My dream is that formal reasoning will become accessible wherever mathematics is used—and that more people will be able to understand, question, and contribute to the knowledge we build. 

Litex is still under rapid development. I hope it can help realize this dream sooner.
