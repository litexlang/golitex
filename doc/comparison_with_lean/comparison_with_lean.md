# Compare Litex with Lean

Mathematics is the art of deriving new facts from established ones. To illustrate, consider a classical syllogism proposed by Aristotle in his Prior Analytics, which formalizes deductive reasoning as follows:

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>set Human</code> <br><br>
      <code>prop self_aware(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$self_aware(x)</code> <br> <br>
      <code>obj Bob Human</code> <br> <br>
      <code>$self_aware(Bob)</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>def Human := Type</code> <br><br>
      <code>def self_aware (x : Human) : Prop := true</code> <br><br>
      <code>axiom self_aware_all :</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;∀ (x : Human), self_aware x</code> <br><br>
      <code>def Bob : Human := Human</code> <br><br>
      <code>example : self_aware Bob := self_aware_all Bob</code>
    </td>
  </tr>
</table>

Consider `Human` as the set of all humans. Using `know`, we establish the fact without the need to be verified by other facts: all humans are self-aware. Since Bob is in the set of `Human`, "Bob is self-aware" is inherently true.

Notice how Litex requires much less typing than Lean4 even in this simple example. An obvious advantage of Litex is that it reduces typing by eliminating the need to name or recall individual facts. When writing done factual expressions for verification, Litex automatically searches for relevant facts, akin to a regular expression search in a large database. For instance, instead of naming an axiom like “axiom self_aware_all,” you simply write “know …”. This approach significantly reduces the cognitive load and enhances efficiency in handling complex logical structures.

Although this is a simple example, it has already taught us how ANY mathematical facts are derived from known facts. Just as Lego lets you assemble complex structures from simple pieces, Litex lets you build math from minimal (with just 8 main keywords: forall, exist, not, or, fn, prop, obj, set and several other auxiliary keywords), reusable parts -— no unnecessary complexity, just pure flexibility.

Also notice Litex adopts a mixture of Python and GoLang's syntax, making it easy to pick up for users who has some programming experience.
