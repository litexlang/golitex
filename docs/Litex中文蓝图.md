# Litex：让数学自我验证的形式化语言

Jiachen Shen and The Litex Team, 2026-07-24. Email: litexlang@outlook.com

官网页面: https://litexlang.com/doc/Litex中文蓝图

## 背景

Litex 是一门以对象和事实为中心的数学形式化语言。它试图降低形式化证明的学习、书写和审阅门槛，让人和 AI 能用接近日常数学的方式表达推理，同时由机器严格检查每条结论。

要理解这个目标为何需要不同的语言设计，可以先看形式化证明与日常数学常见工作流之间的关系。

## 从日常数学的工作流出发

以 Lean 为代表的主流形式化语言已经取得巨大成功，能够严格检查人类和 AI 写出的形式化证明。Lean 的默认交互以最终 Goal 为起点：用户通过 tactic 持续改写、分解或关闭当前 Goal，系统据此构造 proof term，再交给 kernel 检查。

> **Lean tactic：定理先给出最终 Goal → 用户声明应当如何改写、分解或关闭它 → Infoview 显示还剩哪些 Goal → tactic 构造 proof term → kernel 检查该 term。**

以定义序列收敛，证明序列{s(n)}收敛到实数a能推出序列{c * s(n)}能收敛到实数c * a为例

```lean
import Mathlib

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by
    exact div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt
  calc
    |c * s n - c * a| = |c| * |s n - a| := by
      rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) :=
      mul_lt_mul_of_pos_left (hs n ngt) acpos
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm
```

这种证明模式高度通用、抽象且可组合，是 Lean 强大表达能力的重要来源。但它与日常数学书写的默认方向并不完全相同，涉及到大量的tactic关键词；人们更常按下面的顺序推进：

1. 写下对象、定义和条件；
2. 看到一个熟悉的模式；
3. 使用已经知道的事实、定义或计算，写出下一条事实；
4. 让这条事实成为后续推理的上下文。

Litex 把这种日常数学工作流变成它默认的运行逻辑。整个过程可以概括为：

> **Litex：用户声明“什么应当成立” → checker 寻找证明依据 → output 解释该陈述为何以及如何通过验证 → 已验证事实扩展当前上下文 → proof 自下而上生长。**

仍然以序列的例子为例，litex的代码对初学者而言，阅读起来更像日常的数学表达

```litex
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            abs(s(n) - a) < epsilon

prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}

thm converges_to_mul_const:
    ? forall s fn(n N) R, a, c R:
        $converges_to(s, a)
        =>:
            $converges_to(fn(n N) R {c * s(n)}, c * a)
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)}
        abs(c) + 1 > 0
        epsilon / (abs(c) + 1) $in R+
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / (abs(c) + 1), K)}
        witness exist K N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, K)} from N0:
            forall n N:
                n >= N0
                =>:
                    abs(s(n) - a) < epsilon / (abs(c) + 1)
                    abs(c * s(n) - c * a) = abs(c * (s(n) - a)) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < (abs(c) + 1) * (epsilon / (abs(c) + 1)) = epsilon
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
            $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
```

在下面两个维度上，两种默认证明工作流的方向恰好相反。某种意义上，Litex是相反的Lean。

1. **Litex 证明自下而上；Lean tactic 证明自上而下。** 在 Litex 中，每条已验证事实都会扩展上下文，直到积累的事实足以支持结论。Lean tactic 证明通常从最终 Goal 出发，向后往前把它转化为新的 Goal，直到能够由已知事实关闭。

   > 可以把写证明想象成搭乐高：一开始，我们拿到一批可用的积木，以及一个已经完工的成品；任务是证明这些积木确实能够搭出那个成品。Lean tactic 的默认做法像是从目标成品出发，一步步把目标拆了，拆到最后发现拆出来的乐高能和我们可用的积木匹配上，就算证明成功。Litex 的默认做法则像是直接拿起手上的积木一步步拼，直到形成一个和已经完成的成品一样的成品。其中的拼接过程没有那么严格，我们可以从任意角度以任意方式拼，只要形成最后的成品即可。

2. **Litex 用户声明 *what*：“什么应当成立”；Lean tactic 用户声明 *how*：“应当怎样证明 Goal”。** Litex checker 寻找能与结果匹配的证明依据，并解释找到的验证路径。Lean tactic elaboration 按照用户的证明指令构造对应的 proof term，server 显示变化后的 Goal，kernel 检查该 term。

   > 一份完整的乐高说明书同时包含两类信息：第一，这一步应当怎样拼；第二，这一步完成后，整个半成品应当是什么状态。Lean tactic 源码主要记录第一类信息——下一步怎样操作 proof state（沿用上一维度的类比：记录的是这一步我们是怎么拆乐高的）；Litex 源码主要记录第二类信息——这一步推理后得到了什么数学事实（沿用上一维度的类比：记录的是这一步我们是怎么拼乐高的）。

这两个比喻描述的是默认接口的重心，而不是绝对的能力边界。Lean 的机制提供了非常灵活、通用的 proof-programming 环境；Litex 则有意选择更窄的默认交互，让开始写证明更容易，也让源码更接近日常教科书的数学写法。Lean 也支持向前推理，Litex 也提供显式的 goal-directed 证明形式。后文的对照和五个设计目标，会继续展开这两种工作流的异同及各自的取舍。

## 一个完整的小对照：群的单位元唯一性

群的单位元唯一性会把上面两个工作流差异具体化：谁声明结果，谁补出证明路径，以及证明是从最终 Goal 向下分解，还是从已验证事实向上生长。它也展示了定义和证明如何按数学顺序出现，以及结构和载体如何以显式的集合论对象呈现。

### Lean：显式的 record、假设名和 proof script

下面保留问题原有的 `Group` record。原始 `calc` 第一行把 `hright G.one` 用在了 `e = G.mul e G.one` 上；但该假设实际给出的是 `G.mul G.one e = G.one`。下面是与该假设匹配、可通过的改写：

```lean
structure Group where
  Carrier : Type
  mul : Carrier → Carrier → Carrier
  one : Carrier
  inv : Carrier → Carrier
  mul_assoc : ∀ a b c : Carrier, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : Carrier, mul one a = a
  mul_one : ∀ a : Carrier, mul a one = a
  mul_left_inv : ∀ a : Carrier, mul (inv a) a = one

theorem one_unique
    (G : Group)
    (e : G.Carrier)
    (hleft : ∀ a : G.Carrier, G.mul e a = a)
    (hright : ∀ a : G.Carrier, G.mul a e = a) :
    e = G.one := by
  calc
    e = G.mul G.one e := (G.one_mul e).symm
    _ = G.one := hright G.one
```

这是良好的 Lean 代码；它清楚地说明了 proof term 所需的步骤。这里 `hleft` 只是在陈述“`e` 是双侧单位元”时保留下来，最终结论实际只需要候选 `e` 的右单位律和 `G.one` 的左单位律。

下面的 Litex 版本用另一种表面表达同一个结构和唯一性论证。两段代码之后的五个正式 section 会统一解释设计差异，并在每节末尾把一般论点对应回这个例子。

### Litex：结构、局部事实和结论顺着数学叙述写

下面的 Litex 片段已经用 Litex runner 验证通过。

```litex
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one

forall s nonempty_set, G &Group<s>, identity s:
    forall a s:
        G.mul(identity, a) = a
        G.mul(a, identity) = a
    =>:
        identity = G.mul(G.one, identity) = G.one
```

有了这组代码对照，下面五个 section 将依次解释其中的设计差异，并在每节末尾回到这个例子。这样，代码对照和设计论证会始终保持同一套对应关系。

## Litex 是如何实现它的目标的

### 1. 用户声明数学模式与结果，系统寻找具体证明依据

Litex 的默认取向是“模式优先，操作随后”：源码保留可复用的数学结构和应当成立的结果，checker 为当前实例寻找并解释具体证明依据。它首先改变的不是代码长度，而是用户与系统的分工。用户写出 `1 + 1 = 2`、有限集的并仍是有限集、`x^2 >= 0` 这类应当成立的结果；Litex 先检查对象是否良好定义，再从 builtin 规则、已知事实和已知的全称事实中寻找依据。在典型的 Lean tactic 交互中，结论先作为 Goal 给出，用户再逐步指定应当调用什么事实、如何改写或如何分解它，系统据此构造完整的证明。

一个很小的集合命题就能看出这种分工。如果 `s` 是 `t` 的子集，那么它们分别与同一个集合 `u` 取交集后，包含关系仍然保持。Litex 用户可以直接写下这个结果：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

这不是一个留待补全的证明空洞，而是交给 checker 检查的完整事实。它的日常数学读法就是：取 `intersect(s, u)` 的任意成员，它同时属于 `s` 和 `u`；由 `s $subset t` 可知它也属于 `t`，因而属于 `intersect(t, u)`。用户声明应当得到的数学结果，checker 负责从交集成员的展开、成员关系沿子集的传递，以及右侧交集成员的重新组合中寻找验证路径。

*Mathematics in Lean* 的集合章节给出了一个显式展开版本：

```lean
import Mathlib.Data.Set.Lattice

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
end
```

Lean 也能把同一证明写成更精巧的 proof term：

```lean
example {α : Type*} {s t u : Set α} (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩
```

两种 Lean 写法分别展示了显式控制和精巧泛化；后一种甚至更短，并通过 `α` 覆盖任意载体类型。所以差异不在行数，而在默认起点：Litex 鼓励用户先问“下一条应当成立的事实是什么？”，然后直接写下它，不必先掌握 `subset_def` 一类库中定义名或 proof-term 构造。这降低了入门门槛，也让源码更接近日常数学书写。代价是，这些常规推理被移入 Litex checker，因而必须持续测试和审计。

把这个例子推广到一般交互，可以得到下面的分工：

| 默认交互 | 用户源码主要写出 | 交互输出主要补出 |
|---|---|---|
| Lean tactic + server/Infoview | 如何改写、分解或关闭当前 Goal | 每步之后当前还剩哪些 Goal |
| Litex 事实 + checker output | 下一条应当成立的事实或结果 | 该事实为什么通过，以及直接的验证来源 |

简化地说，Lean 的 tactic 源码偏向写 *how*，server output 补出 *what remains*；Litex 源码偏向写 *what*，checker output 补出 *why/how*。这是两种默认交互的重心差异，不是排他性的能力划分：Lean 也能显式写中间结果，Litex 也能组织带 Goal 的证明。

不过，只有 checker 确实能够识别这些常见模式，这种分工才有实际意义。

Litex 目前把数百条这类小而具体的数学模式放在 builtin verification rules 中，覆盖数、等式、序、集合、函数、元组和成员关系等常见情形。它们不是一个不可见的“大自动化按钮”：每条规则都应当有可读的数学含义、实现、测试和可检查的输出理由。具体规则目录会随版本演进，因此这里不把“规则数量”当作稳定的宣传指标。

“每条 builtin rule 都能有相应的 Lean 定理或代码说明”是很好的审计目标，但不能只因规则看起来直观就把它当作已经完成的形式化保证。可信边界、规则实现、回归测试和独立交叉检查都需要持续公开。

这些规则为何应当围绕“模式”组织，可以从日常推理的习惯来理解。

人做数学时经常先认出模式：当前式子和之前的式子相同，或只差一次代入、一次展开、一次实例化。很少有人主要靠记住每一个辅助定理的内部名字来推理。

因此，Litex 会把已经验证的事实放进当前上下文，并尝试匹配和替换。已知的 `forall` 事实在参数条件满足时可以被实例化；已知等式也可以帮助较大的表达式匹配。这不是“猜测证明”：每次成功仍要经过规则和上下文检查。对于真正大型、昂贵或需要读者明确看见依赖的结果，Litex 仍保留具名 theorem 和显式 `by thm` 调用。

在 `Group` 例子中，运算规律直接写在 `<=>:` 里，唯一性证明则直接写成 `identity = G.mul(G.one, identity) = G.one`。
checker 寻找相应的单位律实例和等式方向，因此源码负责声明“什么成立”，验证路径负责说明“为什么成立”。

### 2. 以集合论式对象为表面，而不是要求用户先学习类型宇宙

明确了用户与 checker 的分工后，下一个问题是用户在源码中直接面对什么样的数学对象。

Litex 的表面语言把对象、集合、成员关系、函数和结构都作为普通数学对象来写：对象属于集合；结构是带命名视图的笛卡尔积子集；性质由谓词表达。`s set` 表达的是“`s` 是一个集合”这一数学判断，不是在用户面前再叠一层必须操作的 `Type`、universe 或 proof term。

这不表示语言完全没有约束。函数参数的定义域、返回集合、结构字段和集合成员关系仍会被检查；只是这些约束尽量写在数学家本来就会写的位置。Litex 也保留了 `template` 等参数化构造，因为普通数学确实需要按载体、参数或假设索引的对象族；它并不把自己描述成完整的依赖类型论。

`Group` 例子把这个表面具体化了：`s nonempty_set` 引入载体，`identity s` 表示成员关系，`G &Group<s>` 表示定义在该集合上的结构。
载体约束仍然明确，只是不先把它呈现为需要用户操作的 universe 层级。

### 3. 语法面向数学推理，而非函数式程序构造

对象的表面确定之后，还要决定证明过程以什么语法展开。

一个 Litex 文件的核心动作只有几类：定义对象或概念、检查事实、检查对象是否良好定义、在需要时给出 witness、分类或归纳。普通路线中，用户可以按教材从前到后的顺序写：定义、条件、局部结论、下一条局部结论、定理。

这不等于 Litex 从不需要结构化证明。存在性、反证、分类讨论和归纳仍需要显式写出相应的数学动作。但日常的计算、代入和使用已知规律，不必被拆成“设定目标—调用 tactic—命名中间结果—再调用 tactic”的流水线。语言不应迫使用户为了迎合函数式 proof term 的构造顺序而重排一段本来清楚的数学叙述。

在 `Group` 声明中，乘法写成二元函数 `mul fn(x, y s) s`，使用时写成 `G.mul(x, y)`。
这种写法直接呈现数学上的二元运算，而不要求用户表面的语法先把它表示成一串柯里化的一元函数。

### 4. 既保证严格性，又有可读性和低门槛

更自然的对象和语法，只有在不牺牲严格性的前提下才有意义。

表面接近教材不是放宽标准。每个事实都有 `true`、`unknown` 或 `error` 的结果；检查流程区分表达式是否良好定义、当前上下文是否足够、以及具体是哪条 builtin rule、已知事实或全称事实支持了结论。`trust` 仍是显式注入的假设，不是证明；builtin/infer rules 也是可信计算基的一部分。

所以 Litex 不是 Lean、Coq 或 Isabelle 的替代品。它是在测试一种互补的接口：更小、更可读、以事实为中心的集合论式表面，能否让学生、领域研究者和 AI agent 更便宜地产生、检查和修复有用的形式化数学数据。它是否成功，要由可运行示例、失败记录、测试、规则审计和独立检查来回答，而不是由语法看起来多自然来回答。

`Group` 片段只有在 runner 检查了字段、载体成员关系、结构规律的实例以及等式链的两段之后才会通过。
该片段不含 `trust`；如果显式加入 `trust`，它就会和 checker、builtin/infer rules 一样成为可信边界的一部分。

### 5. 以事实为中心，自下而上建立证明

前四点已经说明了用户与 checker 如何分工、用户面对什么对象、证明如何表达，以及严格性如何维持；最后一点转向证明如何随上下文向前生长。

Litex 是 fact-oriented 的。它默认的推理单位是当前上下文中的下一条数学事实，而不是一个每行都必须立即推进的活跃 Goal。只要一条陈述位于当前作用域中、定义良好，并且能由现有上下文充分支持，checker 就可以接受它、保存它、执行适用的推理，并把增强后的上下文交给后续陈述。因此，Litex 的典型证明会向前、自下而上生长：先建立事实，由它们推出更多事实，直到积累的上下文足以支持最终结论。一条事实可以服务于下一行、很久之后的定理，也可以只作为一条独立的已检查结果。几条数学分支也可以先分别生长，再由之后的陈述让它们汇合。

Lean 通常的交互式定理证明是 goal-directed 的，典型方向是向后、自上而下。最终定理先确定预期类型；局部 term 和 tactic 再在这个预期之下进行 elaboration，逐步把待完成的 Goal 分解或反推为更简单的子目标，直到 Lean 能组装出完整的 proof term。两者的默认问题可以概括为：Lean 问“为了构造当前 Goal，还必须证明什么？”；Litex 问“根据已经建立的上下文，下一条能够推出的事实是什么？”

这是默认工作流的差异，不是绝对的表达能力边界。Lean 可以通过 `have`、局部引理和独立的顶层定理积累前向事实；Litex 也可以用 `claim`、`thm` 等形式组织明确的目标导向证明。改变的是证明展开的方向，不是正确性标准：每条被接受的 Litex 事实仍然必须满足作用域、定义良好性和数学依据的要求。

下面这个局部重写例子可以更直观地展示这种方向差异。在 Lean 中，用户从待证明的 Goal 出发，用每条 `rw` 指定接下来调用哪个事实、按哪个方向匹配和替换：

```lean
-- Using facts from the local context.
example (a b c d g f : ℝ) (h : a * b = c * d) (h' : g = f) :
    a * (b * g) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

对应的 Litex 写法把 Lean 从 Goal 出发执行的四次重写，反过来写成一条等式链。它从 Goal 的右端 `c * (d * f)` 出发，依次写出中间结果，最后到达 Goal 的左端 `a * (b * g)`：

```litex
claim:
    ?forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    c * (d * f) = (c * d) * f = (a * b) * f = a * (b * f) = a * (b * g)
```

1. 第一个等号对应 `rw [mul_assoc]`。
2. 第二个等号对应 `rw [h]`。
3. 第三个等号对应 `rw [← mul_assoc]`。
4. 第四个等号对应 `rw [h']`。

这四个等号与 Lean 的四条 `rw` 恰好逆序对应。Lean 的代码告诉系统“下一步调用哪个事实、朝哪个方向改写 Goal”；Litex 的代码则告诉系统“如果这些推理能够完成，关键的中间结果应当是什么”。checker 再从当前上下文、等式匹配和结构规则中寻找每个相邻等式的依据。

因此，用户不必记住 `mul_assoc` 这样的库名称，也不必显式编排 `h`、`h'` 和结合律的调用顺序与方向，而是写出一条有数学意义的中间结果链。如果一次跳得太远，用户补充的也是中间表达式，而不是指导 checker 一步步怎样搜索。这个例子故意不使用一次完成整个代数推导的自动化，因为这里比较的不是代码长度，而是默认的证明交互方向。

上面的例子涉及代数重写。为了说明这种差异不依赖计算，再看一个让成员关系沿集合包含关系传递的例子。Lean 从目标 `x ∈ c` 出发，通过 `apply` 逐步声明应当怎样证明它：

```lean
import Mathlib

example {α : Type} {A B c : Set α}
    (hAB : A ⊆ B) (hBc : B ⊆ c)
    {x : α} (hx : x ∈ A) :
    x ∈ c := by
  apply hBc
  apply hAB
  exact hx
```

Litex 则直接声明应当建立的中间结果和最终结果，checker 再从当前上下文中寻找它们的依据：

```litex
forall A, B, c set, x A:
    A $subset B
    B $subset c
    =>:
        x $in B
        x $in c
```

对应的 runner trace 把源码没有写出的验证依据补出来；这里只摘录与两个结论直接相关的字段：

```text
"conclusions": [
  {
    "statement": "x $in B",
    "why_verified": {
      "type": "builtin rule",
      "rule": "membership through a known direct set inclusion"
    }
  },
  {
    "statement": "x $in c",
    "why_verified": {
      "type": "builtin rule",
      "rule": "membership through a known direct set inclusion"
    }
  }
]
```

在 Lean 中，用户告诉系统“下一步怎样证”，系统便把 `x ∈ c` 反向分解为 `x ∈ B`，再分解为已知的 `x ∈ A`。在 Litex 中，用户告诉系统“下一个结果是什么”，checker 则从 `x ∈ A` 出发，先确认 `x ∈ B`，再确认 `x ∈ c`。前者典型地从完整 Goal 向前提反向展开，是自上而下的；后者让可验证的事实逐步累积到结论，是自下而上的。

要进一步看清源码与输出如何互补，可以把 Lean 交互中的 Infoview 展开来看。Lean 源码没有把中间 Goal 写成定理内的数学陈述；光标沿 tactic 依次后移时，Infoview 把这一部分补出来。下面省略每一步都不变的 local context：

```text
进入 `by` 后：
⊢ x ∈ c

`apply hBc` 后：
⊢ x ∈ B

`apply hAB` 后：
⊢ x ∈ A

`exact hx` 后：
no goals
```

因此，两种输出恰好补足了两种源码各自没有写出的部分：Litex 源码已经写出 `x $in B` 和 `x $in c`，runner 报告它们为什么通过；Lean 源码写出了如何操作 proof state，Infoview 则报告每步之后还剩什么 Goal。

这两个例子也让“自下而上”变得具体：Lean 从完整 Goal 开始，逐步把它改写或分解到已知事实；Litex 则逐段建立可以确认的等式或成员关系，直到它们支持最终结论。日常数学书写往往也是先记录定义、已知事实和关键中间结果，再让它们汇聚成结论，而不是始终从一个形式化 Goal 出发，把它不断反向分解成子目标。对人和 AI 来说，提出有意义的中间表达式，通常也比持续记忆 `pow_two`、`mul_assoc` 一类库名称及其调用方向更自然。它不表示所有数学发现或证明都严格自下而上；归纳、反证、存在性证明和复杂定理仍可能需要明确的目标结构。

回到 `Group`：结构规律在概念定义时先被验证并保存；候选单位元的规律随后扩展上下文；最后才检查单位元唯一性的等式链。
这个顺序正是上面计算链和集合包含例子共同展示的自下而上模式。

## 总结

Litex 的承诺不应是“省略证明”，而是更严格也更朴素的一件事：让用户先写自己真正想说的数学事实，再让机器把验证、来源和边界清楚地摆出来。

从这个承诺出发，可以把两种取向之间的张力说得更尖锐一些。

> **说得尖锐一点：Lean 常见的 tactic 工作流，就像强制要求你读一本数学书时从最后一页开始读，写一篇论文时从最后一页开始写——先固定最终 Goal，再向后反推前面必须补出什么。**

对于数学探索、学习和教材式叙述而言，这种顺序很别扭。Litex 的设计判断是：它不应成为书写形式化数学时唯一或默认的方式。

不过，当 Litex 把具体证明操作移入 checker 时，压力也随之转向它自己的可信边界。

> **同样尖锐地说：Litex 的第一性原理上最大的问题，是它的可信内核太大。Litex 把数百个常见证明模式放进 builtin 和 infer rules，把工作从用户的 proof script 移进了可信计算基。证明工作并没有消失，只是被系统吸收了。Litex 代码需要能被编译成 Lean 代码，才能确保其正确性。**

正因如此，Litex 需要逐步积累到 Lean 的编译经验。当前仓库只保留了一个很窄的实验接口：它处理 `R` 上已经验证的有理式等式，递归构造分子与分母，再生成由 `ring` 或 `field_simp` 后接 `ring` 检查的 Lean 代码。它还不是覆盖一般 Litex 语句或 builtin rule 的编译器。长期目标仍是：先由 Litex 检查源码，再生成等价的 Lean 陈述和证明，最后由 Lean 独立检查生成结果。

上面的编译目标回应的是可信性问题；回到用户界面，全文反复比较的核心区别仍然是：**Litex 用户声明 *what*：“什么应当成立”；Lean tactic 用户声明 *how*：“应当怎样证明 Goal”。** Litex checker 寻找能与结果匹配的证明依据，并解释找到的验证路径。Lean tactic elaboration 按照用户的证明指令构造对应的 proof term，server 显示变化后的 Goal，kernel 检查该 term。

当人类与 AI 协同工作、能够创造越来越多的数学知识时，形式化系统也应当探索不止一种书写和验证这些知识的方式。从默认交互方向来看，Litex 在某种意义上可以被看作“相反的 Lean”：Lean tactic 通常从最终 Goal 出发，让用户描述如何构造证明；Litex 通常从已建立的事实出发，让用户描述下一个应当得到什么，再由 checker 寻找并解释依据。这不是要取代 Lean，而是为人和 AI 如何编写形式化数学代码，提供另一条值得实践和检验的思路。

由于这条路线仍在研究阶段，当前仓库也应当按开放研究项目来理解：

> Litex 默认公开研究过程和目标，因此仓库会同时保留已经检查的成果、实验以及尚未完成的工作。公开可见不等于宣称完成；每项能力应以当前测试、带日期的状态说明、可信边界和已知限制为准。

相关链接

1. 如果想直接试用例子，查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

3. 如果想查看用Litex书写的数学教科书，可以访问[Litex数学教科书](https://litexlang.com/textbook)。
