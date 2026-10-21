# Litex 的缘起与构建思路

Jiachen Shen, 2026.10.21。中文初稿由作者本人手敲。

Litex围绕这样的想法展开：能不能写下数学，直接得到形式化代码？ 从小我们就知道数学是一种严格的语言，每一句话都能找到相应的佐证来支撑它的正确性。那既然数学本身就是一个严格的语言，为什么不能让数学本身成为一种形式化语言？或者设计一个形式化语言，它在书写上就和日常数学差不多，只是添加一些合理的约束就应该确保其足够结构化，方便去机械地做证明。

这里的观察是，自然语言数学里的许多日常表达，其实已经承担着精确的逻辑责任：

- “任取一个……”确定变量、范围和量词。
- “假设……”引入局部前提，并限定它的有效范围。
- “存在……使得……”要求提供见证，或者提供存在性依据。
- “由定义……”要求表达满足定义中的条件。
- “因此……”要求结论确实能从当前上下文推出。

能不能找到一套语法，让自然语言数学中的对象、条件和推理步骤，与形式化语言里的表达直接对应起来？能不能找到一套运行机制，不但能帮你验证，更能清晰地告诉你每一句话为什么成立？

Litex从第一性原理重新思考数学、自然语言与代码的关系。它想让数学本身成为一种形式化语言。我希望，任何使用数学的人，不论是中小学生还是AI工程师，只需学习少量语言约定，就能从已有的数学表达出发，使用形式化工具，并理解机器检查的依据。

先把这些数学表达与Litex、Lean（最主流的形式化语言）的代码放在一起。进行对比

| 数学表达及其责任 | Litex | Lean |
| --- | --- | --- |
| 任取实数x，假设它大于零，因此它不等于零 | <pre>forall x R:<br>    x > 0<br>    =>:<br>        x != 0</pre> | <pre>example (x : ℝ) (hx : x > 0) : x ≠ 0 := by<br>  exact ne_of_gt hx</pre> |
| 存在一个实数，其平方等于4；取2为见证 | <pre>witness exist w R st {w^2 = 4} from 2</pre> | <pre>example : ∃ w : ℝ, w ^ 2 = 4 := by<br>  refine ⟨2, ?_⟩<br>  norm_num</pre> |
| 由定义，3满足“超过二”的性质 | <pre>prop is_above_two(t R):<br>    t > 2<br><br>by def $is_above_two(3)</pre> | <pre>def isAboveTwo (t : ℝ) : Prop := t > 2<br><br>example : isAboveTwo 3 := by<br>  norm_num [isAboveTwo]</pre> |
| 直接检查一个算式 | <pre>1 + 1 = 2</pre> | <pre>example : (1 : Nat) + 1 = 2 := by<br>  rfl</pre> |
| 定义并调用非零实数上的倒数函数 | <pre>have fn reciprocal(x R: x != 0) R = 1 / x<br>reciprocal(2) = 1 / 2</pre> | <pre>noncomputable def reciprocal (x : {y : ℝ // y ≠ 0}) : ℝ :=<br>  (x : ℝ)⁻¹<br><br>example : reciprocal ⟨2, by norm_num⟩ = (2 : ℝ)⁻¹ := by<br>  simp [reciprocal]</pre> |
| 数系间的成员关系与表示 | <pre>1 $in Z<br>1 $in R<br>1 $in C</pre> | <pre>example : ((1 : ℕ) : ℤ) = (1 : ℤ) := by simp<br>example : ((1 : ℝ) : ℂ) = (1 : ℂ) := by simp</pre> |
| 定义集合，并检查一个成员 | <pre>have multiples_of_four power_set(N) = {a N: a % 4 = 0}<br>4 $in multiples_of_four</pre> | <pre>def multiplesOfFour : Set ℕ := {a &#124; a % 4 = 0}<br><br>example : (4 : ℕ) ∈ multiplesOfFour := by<br>  simp [multiplesOfFour]</pre> |

下面再沿着这些例子，解释Litex的设计思路。Litex希望让用户能尽可能贴近自然语言的方式表达数学，最好能让Litex源码能和想表达的数学一一对应上，同时还不失严格性。（形式化语言大大降低了数学家审稿的时间，但不代表它就是完美无缺的。比如Lean的表面上的表达的东西的意义可能和标准的数学的意义对应不上，这已经成为形式化社区的一个绕不过去的坎了。参见[Faults in Our Formal Benchmarking: Dataset Defects and Evaluation Failures in Lean Theorem Proving](https://arxiv.org/html/2606.29493v1#A5)）

第一个问题是：选择合适的数学公理基础，并确定对象和运算的含义。Lean选择类型论，数学库也为具体运算选择了明确的约定。比如，Lean/Mathlib 把实数除法扩展为全函数，规定 `(1 : ℝ) / 0 = 0`；自然数减法在零处截断，因此 `(1 : Nat) - 2 = 0`（参见 [Division by zero in type theory: a FAQ](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)）。这些是具体编码与数学库的选择，类型论也可以表达受限定义域，Lean的整数减法同样满足 `1 - 2 = -1`。但熟悉的符号带着不同约定时，使用者需要额外确认：形式化陈述表达的，是否还是原来想说的数学。

为了让更多人学会并使用Litex，Litex选择集合论作为它的基础。集合、元素、函数与关系，本来就属于许多人理解数学的方式。这些基本的术语从中学时代就伴随我们直到上班工作。由此出发，我希望把人们在 LaTeX 里惯常写下的数学符号带进语言，连同它们背后的数学关系一并纳入。认出一个交集符号只是开始；系统还需要理解交集如何与属于、包含、相等相联系。在这里，`1 / 0`是会因为不满足良定义性而报错，而`1 - 2 = -1`。

数学词汇就位之后，下一个问题是设计语法。我要让数学语言直接就成为形式化代码：写下对象、定义、条件和推理步骤，让它们在语言中承担相应的作用。更复杂的数学语句用类似Python的缩进组织。下面展开表中的两个例子，看看这种对应具体发生在哪里。

说“任取一个实数x，假设它大于零，那么它不等于零”，可以写成：

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

`forall x R` 对应任取实数x；`=>:` 前面是当前论证的假设，后面是需要证明的结论。假设与x的作用范围都在这个语句内。这里的对应不只是认出几个英文单词，语句的位置和缩进也在表达数学关系。

定义一个非零实数上的倒数函数，并计算一个值，可以写成：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

这里也能逐段对应：`have fn reciprocal` 定义函数，`(x R: x != 0)` 指定参数是非零实数，后面的 `R` 指定值属于实数，`= 1 / x` 给出函数值。调用时，系统需要从当前上下文确认参数满足定义域条件；`reciprocal(0)` 就不能通过这个检查。

这两个例子展示了我希望保留的对应：数学对象、前提、定义域和推理步骤，在代码中各有明确的位置。这里追求的一一对应，是数学含义、推理动作与作用域的对应；普通数学中省略的条件和背景知识，仍需要通过明确的上下文或规则提供。

上面的例子说明怎样写；开头的第二个问题则是：系统怎样检查，并告诉我为什么成立？清晰的语法只是开始，运行机制还要把每句话与它的依据连起来。

当你输入`1 + 1 = 2`，Litex会返回下面这样的单条语句结果。这里节选与解释有关的字段：

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

当你输入 `1 / 0 = 1 / 0`时，结果会指出没有满足的良定义条件。下面同样是字段节选：

```json
{
  "statement_result": "rejected",
  "statement": "(1 / 0) = (1 / 0)",
  "why_failed": {
    "phase": "well_defined",
    "goal": "<well_defined_not_proven>",
    "message": "Could not prove that the statement is well-defined.",
    "diagnostic": {
      "category": "well_defined",
      "message": "Could not prove that the statement is well-defined.",
      "obligation": "0 != 0",
      "expression": "(1 / 0)"
    }
  },
  "stores": [],
  "infers": []
}
```

同样的过程也适用于前面的倒数函数。检查 `reciprocal(2) = 1 / 2` 时，参数需要满足 `2 != 0`，然后才能使用函数定义检查等式；换成 `reciprocal(0)`，就缺少定义域所要求的非零条件。检查存在性见证时，要确认见证属于指定集合并满足相应性质；检查 `by def $is_above_two(3)` 时，要确认定义中的 `3 > 2`。

我希望这些数学依据能被系统直接展示。上面的输出就说明，`1 + 1 = 2`由`Closed calculation`这个规则检查出来；除以零的例子则指出无法满足的条件（Litex的输出涵盖中文、英文等10种语言）。用户写出数学对象与步骤，检查器返回找到的依据，或者指出当前缺少的条件与证明。结构化的验证记录还需要适合读者的呈现，才能成为清晰的教学解释。

> 更多信息：Litex的`litex -session`交互模式，像Python的REPL那样，语句失败了但还能保留已经接受的定义和事实。就像打草稿一样，写错了不要紧，只有做对的事情才会被保留下来成为后续输入的上下文。例如你已经接受了 `let a = 2`，接着试 `a = 3` 会失败，但同一 session 里仍可用刚才的 `a` 去验证 `a + 1 = 3`——失败的那一步丢掉，做对的上下文留下。常见的 Lean 文件工作流里，改一处往往还要再跑一遍相关检查；Litex 把“增量保留已接受事实”做成了默认体验。这样的交互方式非常适合Litex和AI Agent交互地批量化生成证明。

我希望Litex像身边的一个严格的老师：检查通过时，说明所用依据；没有通过时，指出当前无法证明的地方。找不到证明，并不等于这句话在数学上是错的。

这一选择塑造了验证引擎。在典型Lean的 tactic 工作流里，作者给出构造证明的指令，最终由内核检查。Litex 把“下一条数学事实”放在交互的中心：给定当前上下文，系统能否为这个陈述辩护？这是关于默认写作体验的选择：Lean 的文档说明了它自己的 [elaboration 与检查模型](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)，它默认用户写how to prove的tactic串，由Lean来告诉你what to prove；Litex默认用户写what to prove的证明过程，由Litex来告诉你how to prove的。

Litex内部有600多个内置规则（Litex有了几十种对象如`1`这样的数字，`+`这样的函数，`union`这样的集合操作符号，几十种语句，如`let a = 1`这样的定义语句，几十种事实，比如`1 < 2`这样的不等式，`exist x R st {x > 1}`这样的存在性事实，`forall a Z => a $in R`这样的全量事实等）和复杂的分层的递归的验证过程帮你找到对应的证明方式，只要你的上下文足够（不能跳步太多，否则Litex搜索的引擎找不到也推理不出你想证明的事情）。

实现这"基于上下文找到对应的事实，用适当的规则来验证每一步"的基本逻辑很直观：匹配与代换。找到相关的已知事实，与正在检查的陈述做匹配，再判断所需的代换与条件是否成立。这个想法后来发展成：结构化的事实查找、有界递归验证、内置数学规则，以及引入见证或分情形等显式的证明步骤陈述。本质上这是一个超级数学特化的搜索引擎。

有了内置的规则，我们要做的事情就是，读入用户的输入，判断出来要用哪些规则和上下文，来验证这个输入的正确性。如果我找不到上下文，或者找不到对应的规则，就证明不出来。比如`a = 1`是`unknown`的，因为我不知道a是什么。只有你定义了`let a = 1`，这时候你再输入`a = 1`，litex才能帮你找到对应的上下文进而证明出来`a = 1`。

数学的常见对象非常非常多，语句也很多，但毕竟是有限的，Litex的一大贡献是，通过2年的不断摸索，把对象之间的常见关系，语句之间的常见关系，串联起来了，让日常的数学表达真的能几乎1比1被视作Litex语句了。每个常见的数学对象，有自己的定义，有自己的和其他对象的关系，这些都被做成600多个内置规则留在litex里了。用户不需要考虑这些很琐碎（trivial）的东西。

但检查一条陈述，只是我想要的一部分。我还希望系统返回对验证过程的解释：它用了哪些事实、哪些规则把它们连起来、哪一步无法被辩护。所以Litex有一个数学特化的搜索引擎，专门在这个为数学特化的数据库结构上工作，在支持的范围内，根据上下文和内置规则寻找陈述成立的依据，并报告验证失败的位置。

<img src="https://litexlang.com/assets/diagrams/litex-verification-pipeline-v2.png" alt="Litex verification pipeline" style="max-width: 80%; height: auto;" />

litex能把常见的数学表达一步步解析成机器可识别可存储可调用的数学知识，是很难的，这个功能是Litex项目的核心，也是Litex多达20多万行Rust源代码的内核所做的（一边探索自己在完成什么，一边构建工程，花了我两年，在AI的帮助下，这个工程的细节才能完备完善。虽然我是内置了上百个快捷键的程序员，但没有ai帮助也不可能完成如此大的工程。）。为了把这些表达、上下文与验证依据连在一起，我自行开发了Litex的数学特化数据库和搜索引擎。现在，这个流程不只是能做验证，还能输出结果，告诉你为什么这些数学语句能成立。这也让我想到数学教育：我们可以构建可交互的数学书，数学书以接近自然数学表达的Litex源码出现，每句经过验证的语句都能对应一份“为什么成立”的结构化信息。所有的结构化信息连起来，就成了一张网，帮助读者理解数学概念之间怎样互相连接。这个过程可能会改变读者对数学、代码与证明的看法。

用一个年龄小例子把这条链摊开：同一份推理，依次落成 Litex 源码、说明依据的 JSON、以及 `-lean` 生成的 Lean（当前为预览编译；下表 Lean 列为真实输出的节选）。

```litex
let my_age = 3
let brother_age = 3 * my_age
brother_age = 3 * 3 = 9
```

| Litex 源码 | JSON（验证结果摘要） | Lean（`-lean` 节选） |
| --- | --- | --- |
| `let my_age = 3`<br>`let brother_age = 3 * my_age`<br>`brother_age = 3 * 3 = 9` | <pre>{<br>  "statement_result": "accepted",<br>  "statement": "brother_age = (3 * 3) = 9",<br>  "proof_method": {<br>    "type": "compound_fact",<br>    "rule_name": "Chain"<br>  },<br>  "stores": [<br>    "brother_age = (3 * 3) = 9",<br>    "brother_age = (3 * 3)",<br>    "(3 * 3) = 9"<br>  ]<br>}</pre> | <pre>noncomputable def _object_i1 :=<br>  Litex.number (M := M) (3 : ℂ)<br><br>theorem h_1 :<br>  Litex.Same (_object_i1 …)<br>    (Litex.number … (3 : ℂ)) := …<br><br>-- … 中间略 …<br><br>theorem h_470 :<br>  Litex.Same (_object_i2 …)<br>    (Litex.number … (9 : ℂ)) := …</pre> |

左边是人写的数学；中间是机器存下来的“为什么成立”；右边是同一结果接到 Lean 后的证明形态。可交互数学书吃的是中间这一列；要独立复核时，再走到右边。

一旦验证产出结构化的记录，进一步的可能就出现了。
定义与已建立事实之间的关系可以支撑知识图谱；AI agent 可以用反馈修正失败的一步，并从已接受的知识继续。围绕这种交互构建一个有能力的数学 agent，是我更长远的目标之一。

同一份记录也为通往 Lean 的桥梁提供了基础。编译器可以同时利用 Litex 源码及其验证结果，按 Litex 实际使用的推理生成 Lean 陈述与证明。有人会问，Litex源码这么多，是不是有Bug，有Bug是不是说明不严格？Litex当然会有bug，但Litex代码能编译到Lean。可以这样去理解：一般的形式化语言，比如Lean，需要被编译成lambda calculus，以确保里面的代码的严格性；而Litex，能被编译成Lean，确保正确性。这里还能看到抽象层级的区别：Litex可以理解成Lean的某种封装。

而因为Litex的执行不用触及lambda calculus这么底层的东西（lean的验证和执行本质上是一体的，都是靠编译到lambda calculus的。Litex的验证天然分成了两层，首先是litex帮你验证了一遍这一轮，通常你已经能觉得你证明完毕了；其次是如果你真的想要绝对无误（因为你可能担心litex的验证逻辑有bug），那就让litex帮你编译到lean代码再验证。litex帮你验证的这一轮可以非常快），本质上技术架构上是一种数据库和搜索，所以Litex在一些任务上非常快。下面是一次本地抽查（2026-10-21）：Litex 用 `target/release/litex -f`，Lean 在已有 Mathlib 缓存的工程里用 `lake env lean` 检查同一批小例子；Lean 时间为第二次较暖运行。这不是正式 benchmark，详细条件与公平阅读说明见[Lean–Litex 示例对比](Lean与Litex示例对比.md#9-local-runtime-spot-checks)。

| 场景 | Litex（中位） | Lean（第 2 次较暖） | 量级差 |
| --- | --- | --- | --- |
| 短算术 / `x = 2` ⇒ `x + 1 = 3`，`x^2 = 4` | ~6 ms | ~7 s | ~1000× |
| 二元一次方程计算链 | ~16 ms | ~30 s | ~2000× |
| 集合：交保持包含 `{1,2} ∈ {{}, {1,2}}` | ~4 ms | ~3.4 s | ~800× |
| 大数见证 `witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481` | ~5 ms | ~16–21 s（`norm_num` / `native_decide` 都慢） | ~3000×+ |
| 对照：Lean 无 Mathlib 的 `1 + 1 = 2` | — | ~2.3 s（仅 `lake env lean` 启动） | Litex 整文件仍约数毫秒 |

Litex能编译到Lean有巨大价值。它给 Litex 一条进入 Lean 生态的路径，并为翻译后的证明增加一层独立检查。Lean一直以难以被阅读著称，它的语义和标准数学语义也有一些冲突。Litex相当于提供了门槛更低的，让普通人使用形式化工具的一种途径：熟悉的表层与快速检查在 Litex；更深的库与独立内核复核可以接到 Lean。更完整的并排例子见[Lean–Litex 示例对比](Lean与Litex示例对比.md)；设计总论见[Litex 中文蓝图](Litex中文蓝图.md)。

虽然做数学研究的评价体系受到了AI冲击，但我觉得现在是学习数学的最好的时候（相关讨论见 3Blue1Brown 的[《There's never been a better time to go into math》](https://www.youtube.com/watch?v=LKrwhjOI8Nc)）。普通人不需要做数学，他们只需要使用数学，把数学当做他们理解世界的工具。AI并没有促进人们理解数学，在帮人学习上，本质上还是一种电子化的做题家老师。但AI让Litex这样的项目得以快速实现，Litex从第一性原理上，重新审视了什么是数学，什么是推理这样的问题。希望学习过Litex的读者，未来看到自然语言写的数学，也能联想到Litex，联想到数学本身也是一个严格的语言，它有它背后的逻辑和脉络。我想就够了。

Litex 仍在快速开发中。欢迎大家使用并提出宝贵建议。官网：https://litexlang.com/。开源代码在https://github.com/litexlang/golitex。想要了解litex怎么工作的，可以联系litexlang@outlook.com。
