<div align="center">
<img src="./logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Scale Formal Reasoning in AI Age

**version v0.1.10-beta (not yet ready for production use)**  
*Jiachen Shen and The Litex Team*

[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Official Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.org)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Online Playground](https://img.shields.io/badge/Online%20Playground-darkgreen?logo=playground)](https://litexlang.org/playground)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/litexlang/golitex)

</div>

## Litex: The Simplest Formal Language

*Visit [Official Website](https://litexlang.org/) to learn more about Litex. Visit [Tutorial](https://litexlang.org/doc/Tutorial/Introduction) to learn how to use Litex and try some examples. Visit [Start](https://litexlang.org/doc/Start) to start using Litex (online, locally, in Python, in Jupyter Notebook, etc.).*

Litex is an intuitive and scalable formal language for coding reasoning. It ensures every step is correct, and can be learned by anyone in 1–2 hours, even without math or programming background.

Formal language turns writing math into writing code, enabling automation, collaboration, and standardization. With AI generating reasoning and Litex verifying it, automated reasoning becomes a reality.

Traditional formal languages are too complex. Litex lowers the barrier by 10x, making formalization as easy and fast as natural writing. Here is an comparison between Litex and Lean 4 (a traditional formal language) about proving the irrationality of sqrt(2).

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>claim:</code><br>
      <code>&nbsp;&nbsp;not sqrt(2) $in Q</code><br>
      <code>&nbsp;&nbsp;prove_by_contradiction:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have x, y st $Q_representation_in_fraction(sqrt(2))</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x = sqrt(2) * y</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x ^ 2 = (sqrt(2) ^ 2) * (y ^ 2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;sqrt(2) ^ 2 = 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;x ^ 2 = 2 * (y ^ 2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, x ^ 2) = log(2, 2 * (y ^ 2))</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, x ^ 2) = 2 * log(2, x)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, y ^ 2) = 2 * log(2, y)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, 2 * (y ^ 2)) = log(2, 2) + log(2, y ^ 2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, 2) = 1</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, 2 * (y ^ 2)) = 1 + log(2, y ^ 2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;log(2, x ^ 2) = 1 + 2 * log(2, y)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;2 * log(2, x) = 1 + 2 * log(2, y)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(2 * log(2, x)) % 2 = (1 + 2 * log(2, y)) % 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(2 * log(2, x)) % 2 = 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;0 = (1 + 2 * log(2, y)) % 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;(1+2 * log(2, y)) % 2 = 1 % 2 + (2*log(2, y)) % 2</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;1 % 2 + (2 * log(2, y)) % 2 = 1 + 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;0 = 1</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>theorem sqrt2_irrational :</code><br>
      <code>&nbsp;&nbsp;¬ ∃ a b : ℕ, a.gcd b = 1 ∧ a * a = 2 * b * b := by</code><br>
      <code>&nbsp;&nbsp;intro h</code><br>
      <code>&nbsp;&nbsp;obtain ⟨a, b, hcop, h⟩ := h</code><br><br>
      <code>have ha_even : Even a := by</code><br>
      <code>&nbsp;&nbsp;rw [Nat.mul_assoc] at h</code><br>
      <code>&nbsp;&nbsp;have : Even (a * a) := by rw [h]; exact even_mul_right b b</code><br>
      <code>&nbsp;&nbsp;exact even_of_even_sq this</code><br><br>
      <code>obtain ⟨k, hk⟩ := ha_even</code><br><br>
      <code>have h2 : 2 * k * k = b * b := by</code><br>
      <code>&nbsp;&nbsp;rw [hk, ←mul_assoc, ←mul_assoc, mul_comm 2 2, ←mul_assoc] at h</code><br>
      <code>&nbsp;&nbsp;apply Nat.mul_right_cancel (Nat.zero_lt_succ _)</code><br>
      <code>&nbsp;&nbsp;rw [←h, ←mul_assoc, ←mul_assoc]</code><br>
      <code>&nbsp;&nbsp;rfl</code><br><br>
      <code>have hb_even : Even b :=</code><br>
      <code>&nbsp;&nbsp;even_of_even_sq (by rw [←h2]; exact even_mul_left _ _)</code><br><br>
      <code>obtain ⟨m, hm⟩ := hb_even</code><br><br>
      <code>have : a.gcd b ≠ 1 := by</code><br>
      <code>&nbsp;&nbsp;rw [hk, hm]</code><br>
      <code>&nbsp;&nbsp;have : (2 * k).gcd (2 * m) = 2 * (k.gcd m) := Nat.gcd_mul_left_right</code><br>
      <code>&nbsp;&nbsp;apply Nat.ne_of_gt</code><br>
      <code>&nbsp;&nbsp;apply Nat.mul_pos (by decide)</code><br>
      <code>&nbsp;&nbsp;exact Nat.gcd_pos_left m (by decide)</code><br><br>
      <code>contradiction</code>
    </td>
  </tr>
</table>

The simplicity of Litex enables both the large-scale adoption of formal languages and their deep integration into AI systems. In Litex, there is no foreign keywords, twisted syntax, or complex semantics, just plain reasoning. Litex benefits both AI research and the math community. 

## Contact & Contribute to Litex

Hi, I’m Jiachen Shen, creator of Litex. You’re warmly invited to join the Litex community and grow with us. Our key directions:

Dataset – from elementary problems to IMO, textbooks, and research papers. This dataset powers AI training and reasoning.

Litex + AI – embedding Litex into AI workflows to make reasoning scalable, reliable, and 10x more accessible.

MAKE MONEY BY CONTRIBUTING! Visit [Task Board](https://litexlang.org/task-board) to earn by solving tasks, or [Collaboration](https://litexlang.org/collaboration) to discuss bigger projects.

Contact me via [email](mailto:litexlang@outlook.com) or join the [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/).

## Special Thanks

Throughout this journey of designing, implementing, and growing Litex into a community, I (Jiachen Shen, creator of Litex) have been fortunate to receive tremendous help from friends and colleagues. Without their support, Litex would not have had the chance to succeed.

I owe special thanks to my coworker Zhaoxuan Hong, who built Litex’s powerful toolchains and has supported the project from the very beginning. The Litex project is also deeply grateful to Siqi Sun, Wei Lin, Peng Sun, Jie Fu, Zeyu Zheng, Huajian Xin, Zijie Qiu, Sheng Xu, Siqi Guo, Haoyang Shi, and Chengyang Zhu for their invaluable contributions.

Moreover, I cannot fully express my gratitude to all those who have actively contributed to the Litex community. I am certain this list of special thanks will only grow longer in the future.

We warmly invite you to join us. The best way to predict future is to create it. Let’s build the future together!