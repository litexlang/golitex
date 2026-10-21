# Motivation and Construction Thinking Behind Litex

Website: https://litexlang.com/doc/Motivation_and_Construction_Thinking_Behind_Litex

Chinese version: https://litexlang.com/doc/Litex的缘起与构建思路

Litex starts from a question: can we write mathematics and get formal code directly? From an early age, we learn that mathematics is a rigorous language: each statement needs grounds to justify its correctness. If mathematics is already a rigorous language, why couldn't mathematics itself be a formal language? Could we design one whose writing closely resembles everyday mathematics, adding reasonable constraints to make it structured enough to support mechanical proof?

This is an attempt to rethink the relationship between mathematics, natural language, and code from first principles—and, through that, to rethink what mathematics is and what proof means. Litex grew out of that curiosity. It aims to make mathematics itself a formal language, so that anyone who uses mathematics, from school students to AI engineers, can also use formal tools directly, without specialized training.

Here is the thinking behind Litex's design.

The first question is choosing a suitable mathematical foundation and its axioms. Every formal language relies on particular mathematical axioms, and the choice of foundation directly shapes the language. Consider Lean as a point of comparison. Lean uses type theory, an abstract and coherent mathematical foundation supporting a powerful, programmable system. Some of its default conventions differ substantially from everyday mathematics. For example, Lean/Mathlib makes real division total, with `(1 : ℝ) / 0 = 0`; natural-number subtraction truncates at zero, so `(1 : Nat) - 2 = 0`. Such choices can leave people thinking they have proved A when they have actually proved a slightly different B, because familiar mathematical notation may mean something different in Lean. This can make learning and using formal tools feel out of reach for ordinary users.

To help more people learn and use Litex, I chose set theory as its foundation. Sets, elements, functions, and relations already belong to the way many people understand mathematics. These basic terms stay with us from secondary school into our working lives. From there, I wanted to bring familiar mathematical notation—the symbols people routinely write in LaTeX—into the language, together with the mathematical relationships behind it. Recognizing an intersection symbol is only the beginning; the system also needs to understand how intersection relates to membership, inclusion, and equality. Here, `1 / 0` is rejected because it is not well-defined, while `1 - 2 = -1`.

With the mathematical vocabulary in place, the next question is syntax design. I want mathematical language itself to become formal code. Statements such as `1 + 1 = 2` and `forall x, y R: x >= 0 and y >= 0 => x + y >= 0` can run directly in Litex. More complex mathematical statements are organized using syntax similar to Python's. Users write what they want to prove, and Litex explains whether it can justify the statement, and why. When you enter `1 + 1 = 2`, Litex returns a statement result like this:

```json
{
  "statement_result": "accepted",
  "statement": "(1 + 1) = 2",
  "proof_method": {
    "type": "by_closed_calculation",
    "rule_name": "Closed calculation",
    "message": "Exact evaluation of closed expressions without proof search"
  },
  "stores": [
    "(1 + 1) = 2"
  ],
  "infers": []
}
```

The benefit is clean, readable Litex source. Users can see at a glance what they are trying to prove and what they have already proved. Litex's output explains why it can or cannot justify each statement. Reading and writing Litex source could then become as direct as writing everyday mathematics.

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
