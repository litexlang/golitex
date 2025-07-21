## Litex: Scale Formal Reasoning In AI Age

**Litex是一门简单直观的形式化语言，用代码精确表达数学与推理，并确保逻辑严谨。用Litex构建形式化数据的成本和门槛比主流形式化语言如Lean低10倍。我们希望它能成为支撑 AI 推理能力和安全性的关键基础设施。**

**Litex的推荐人包括了DeepSeek-Prover一作辛华剑，Moss一作孙天祥，DeepSeek数据组员工张洺川，获得多轮融资的AI创业者孙思琦、孙鹏，图灵奖得主Bengio的博后现任AILab安全组研究员付杰，潘建伟团队量子编译器创业者黄冲，奇绩校友陈小杨。创始人沈嘉辰的导师林伟是复旦数学系教授兼教务处处长。**

下面我们举例说明，相比主流形式化语言如Lean，**简单直观的Litex把构建形式化数据的成本和门槛降低了10倍**。欢迎访问官网沙盒[1]，运行这里的例子和更多例子。

例1：多元线性方程组：解方程 2x + 3y = 10 和 4x + 5y = 14。本例说明了，日常数学在Litex中可以很直观地表达，没有任何门槛。

<table style="border-collapse: collapse; width: 100%; font-size: 10px;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 30%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 70%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px;line-height: 1.5">
      <code>obj x R, y R:</code><br>
      <code>&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
      <code>&nbsp;&nbsp;4 * x + 5 * y = 14</code><br>
      <code>2 * (2 * x + 3 * y) = 2 * 10</code><br>
      <code>4* x + 6 * y = 2 * 10</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = 2 * 10 - 14</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = y</code><br>
      <code>y = 6</code><br>
      <code>2 * x + 3 * 6 = 10</code><br>
      <code>2 * x + 18 - 18 = 10 - 18</code><br>
      <code>2 * x + 18 - 18 = -8</code><br>
      <code>(2 * x) / 2 = -8 / 2</code><br>
      <code>(2 * x) / 2 = x</code><br>
      <code>x = -4</code>
    </td>
    <td style="border: 2px solid black; padding: 2px;line-height: 1.5">
      <code>import Mathlib.Tactic</code><br>
      <code>example (x y : ℝ) (h₁ : 2 * x + 3 * y = 10) (h₂ : 4 * x + 5 * y = 14) : x = -4 ∧ y = 6 := by</code><br>
      <code>&nbsp;&nbsp;have h₃ : 2 * (2 * x + 3 * y) = 2 * 10 := by rw [h₁]</code><br>
      <code>&nbsp;&nbsp;have h₄ : 4 * x + 6 * y = 20 := by linear_combination 2 * h₁</code><br>
      <code>&nbsp;&nbsp;have h₅ : (4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14 := by</code><br>
      <code>&nbsp;&nbsp;rw [h₄, h₂]</code><br>
      <code>&nbsp;&nbsp;have h₆ : (4 * x + 6 * y) - (4 * x + 5 * y) = y := by</code><br>
      <code>&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;have h₇ : 20 - 14 = 6 := by norm_num</code><br>
      <code>&nbsp;&nbsp;have h₈ : y = 6 := by</code><br>
      <code>&nbsp;&nbsp;rw [←h₆, h₅, h₇]</code><br>
      <code>&nbsp;&nbsp;have h₉ : 2 * x + 3 * 6 = 10 := by rw [h₈, h₁]</code><br>
      <code>&nbsp;&nbsp;have h₁₀ : 2 * x + 18 = 10 := by</code><br>
      <code>&nbsp;&nbsp;rw [mul_add] at h₉</code><br>
      <code>&nbsp;&nbsp;simp at h₉</code><br>
      <code>&nbsp;&nbsp;exact h₉</code><br>
      <code>&nbsp;&nbsp;have h₁₁ : 2 * x = -8 := by</code><br>
      <code>&nbsp;&nbsp;linear_combination h₁₀ - 18</code><br>
      <code>&nbsp;&nbsp;have h₁₂ : x = -4 := by</code><br>
      <code>&nbsp;&nbsp;linear_combination h₁₁ / 2</code><br>
      <code>&nbsp;&nbsp;exact ⟨h₁₂, h₈⟩</code>
    </td>
  </tr>
</table>

| 方面         | Litex                          | Lean                                                         |
| ------------ | ------------------------------ | ------------------------------------------------------------ |
| **书写**     | 贴近日常数学表达，无需翻译   | 语法不直观。数学本身是一门很难的学科，而翻译成Lean的工作量甚至比思考数学本身还大得多。Lean的库只能部分减轻其负担 |
| **阅读**     | 未经训练的普通人就能直观地理解 | 需掌握 tactic / type / rw / ring / simp / exact / ring_exp / norm_num 等。初等方程尚且如此，可想而知进阶数学有多复杂 |
| **语义**     | 每步清晰语义，AI 易训练与验证  | 严重依赖复杂的 tactic，需要给一切已知事实取名字记忆，严重增加用户负担，不同数学领域有不同常用词，学习成本极高 |
| **门槛**     | 初中生即可上手，适合众包       | 用Lean训练 AI 的研究者，也只有不到20%能理解模型生成的证明过程，只能依赖 API 进行验证，难以掌控模型实际学到了什么 |
| **数据成本** | 接近正常写数学                | 陶哲轩提到，Lean的表达复杂度10倍于正常写数学。如果能将成本降低到1倍，形式化所有数学书、知识的时机就成熟了[2] |

例2：证明根号2是无理数，思路是假设根号2可以表示为分数，然后推导出矛盾。本例说明了，Litex的表达能力很强，且很贴近自然语言的表达。用Litex书写的代码，和日常人们写在论文、教科书上的几乎一样。

<table style="border-collapse: collapse; width: 100%; font-size: 10px;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px;line-height: 1.5">
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
    <td style="border: 2px solid black; padding: 2px;line-height: 1.5">
      <code>theorem sqrt2_irrational :</code><br>
      <code>&nbsp;&nbsp;¬ ∃ a b : ℕ, a.gcd b = 1 ∧ a * a = 2 * b * b := by</code><br>
      <code>&nbsp;&nbsp;intro h</code><br>
      <code>&nbsp;&nbsp;obtain ⟨a, b, hcop, h⟩ := h</code><br>
      <code>have ha_even : Even a := by</code><br>
      <code>&nbsp;&nbsp;rw [Nat.mul_assoc] at h</code><br>
      <code>&nbsp;&nbsp;have : Even (a * a) := by rw [h]; exact even_mul_right b b</code><br>
      <code>&nbsp;&nbsp;exact even_of_even_sq this</code><br>
      <code>obtain ⟨k, hk⟩ := ha_even</code><br>
      <code>have h2 : 2 * k * k = b * b := by</code><br>
      <code>&nbsp;&nbsp;rw [hk, ←mul_assoc, ←mul_assoc, mul_comm 2 2, ←mul_assoc] at h</code><br>
      <code>&nbsp;&nbsp;apply Nat.mul_right_cancel (Nat.zero_lt_succ _)</code><br>
      <code>&nbsp;&nbsp;rw [←h, ←mul_assoc, ←mul_assoc]</code><br>
      <code>&nbsp;&nbsp;rfl</code><br>
      <code>have hb_even : Even b :=</code><br>
      <code>&nbsp;&nbsp;even_of_even_sq (by rw [←h2]; exact even_mul_left _ _)</code><br>
      <code>obtain ⟨m, hm⟩ := hb_even</code><br>
      <code>have : a.gcd b ≠ 1 := by</code><br>
      <code>&nbsp;&nbsp;rw [hk, hm]</code><br>
      <code>&nbsp;&nbsp;have : (2 * k).gcd (2 * m) = 2 * (k.gcd m) := Nat.gcd_mul_left_right</code><br>
      <code>&nbsp;&nbsp;apply Nat.ne_of_gt</code><br>
      <code>&nbsp;&nbsp;apply Nat.mul_pos (by decide)</code><br>
      <code>&nbsp;&nbsp;exact Nat.gcd_pos_left m (by decide)</code><br>
      <code>contradiction</code>
    </td>
  </tr>
</table>

例3：定义抽象代数中的概念：群，并证明实数、整数构成群。本例说明了，进阶数学的证明，在Litex中也能很直观地表达。Litex的代码涉及到的概念和标准的教科书上一样多，而不是像Lean那样，需要引入额外概念只是为了Lean自身能运行。

<table style="border-collapse: collapse; width: 100%; font-size: 10px;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>prop is_group(s set, mul fn(s, s)s, inv fn(s)s, e s):</code><br>
      <code>&nbsp;&nbsp;forall x s, y s, z s:</code><br>
      <code>&nbsp;&nbsp;mul(mul(x, y), z) = mul(x, mul(y, z))</code><br>
      <code>&nbsp;&nbsp;forall x s:</code><br>
      <code>&nbsp;&nbsp;mul(x, inv(x)) = e</code><br>
      <code>&nbsp;&nbsp;mul(inv(x), x) = e</code><br>
      <code>fn inverse(x R)R:</code><br>
      <code>&nbsp;&nbsp;inverse(x) + x = 0</code><br>
      <code>forall x R:</code><br>
      <code>&nbsp;&nbsp;inverse(x) $in R</code><br>
      <code>&nbsp;&nbsp;x + inverse(x) = inverse(x) + x</code><br>
      <code>&nbsp;&nbsp;inverse(x) + x = 0</code><br>
      <code>&nbsp;&nbsp;x + inverse(x) = 0</code><br>
      <code>$is_group(R, +, inverse, 0)</code><br>
      <code>$is_group(Z, +, inverse, 0)</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>structure MyGroup (G : Type) where</code><br>
      <code>&nbsp;&nbsp;add : G → G → G</code><br>
      <code>&nbsp;&nbsp;zero : G</code><br>
      <code>&nbsp;&nbsp;neg : G → G</code><br>
      <code>&nbsp;&nbsp;add_assoc : ∀ a b c : G, add (add a b) c = add a (add b c)</code><br>
      <code>&nbsp;&nbsp;zero_add : ∀ a : G, add zero a = a</code><br>
      <code>&nbsp;&nbsp;add_zero : ∀ a : G, add a zero = a</code><br>
      <code>&nbsp;&nbsp;add_left_neg : ∀ a : G, add (neg a) a = zero</code><br><br>
      <code>def intAddGroup : MyGroup Int where</code><br>
      <code>&nbsp;&nbsp;add := Int.add</code><br>
      <code>&nbsp;&nbsp;zero := 0</code><br>
      <code>&nbsp;&nbsp;neg := Int.neg</code><br>
      <code>&nbsp;&nbsp;add_assoc := by intros; apply Int.add_assoc</code><br>
      <code>&nbsp;&nbsp;zero_add := by intros; apply Int.zero_add</code><br>
      <code>&nbsp;&nbsp;add_zero := by intros; app ly Int.add_zero</code><br>
      <code>&nbsp;&nbsp;add_left_neg := by intros; apply Int.neg_add_self</code><br>
      <code>-- R is not builtin in Lean, the user has to define it himself or rely on the library. We skip it.</code><br>
    </td>
  </tr>
</table>

2025 年，AI 正在经历范式转变：一方面，以形式化语言为价值函数的强化学习显著增强了推理能力；另一方面，AI 正迈入 Agent 时代，开始主动干预现实，带来效率跃迁与安全挑战。投资公司 ARIA 已投资 5900 万英镑，押注形式化语言构建可信 AI。但 Lean、Coq 等语言门槛极高。DeepSeek, OpenAI等纷纷下场投入巨资构建形式化数据集仍进展迟缓。Lumina 为每道 IMO 题开价 105 美元也难觅接单，社区数据仍稀缺。形式化语言的构建速度，正成为 AI 能力发展的巨大瓶颈。**如果Litex能成为主流形式化语言，作为Litex开发者的我们将在构建形式化数据集和工具链方面建立显著优势。一旦Litex发展成为AI基础设施标准，我们将掌握重要的技术话语权，形成可持续的商业生态。**

<div style="font-size: 11px; line-height: 1.1; border-collapse: collapse; width: 100%;">
[1] 官网沙盒: https://litexlang.org/playground . 源代码：https://github.com/litexlang/golitex . 邮件联系：litexlang@outlook.com. 复旦数学博二在读的沈嘉辰是Litex发明人，洪昭宣是Litex工具的开发者。
</div>

<div style="font-size: 11px; line-height: 1.1; border-collapse: collapse; width: 100%;">
[2] 陶哲轩关于AI和形式化语言如何改变数学的采访 https://www.scientificamerican.com/article/ai-will-become-mathematicians-co-pilot/
</div>