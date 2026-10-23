# Litex 的缘起与构建思路

Jiachen Shen, 2026.10.21。中文初稿由作者本人手敲。

官网：https://litexlang.com/

Github: https://github.com/litexlang/golitex

## Litex是什么

Litex is a novel formal language where its source code stay close to natural language and runs 10-100x faster than Lean in some very common mathematical statements. By rethinking the relationship between math, code, and reasoning, Litex might significantly lower the barrier of using formal language tools both for humans and AIs.

先把这些数学表达与Litex、Lean（最主流的形式化语言）的代码放在一起。进行对比。可以看到很多日常的数学表达，在Litex里直接就是合法的语句，因此学习和使用Litex的门槛是非常低的。

Lean 例子均使用 `import Mathlib`。

| 数学表达及其责任 | Litex | Lean |
| --- | --- | --- |
| **任取实数x，假设它大于零，因此它不等于零** | `forall x R:` | `example (x : ℝ) (hx : x > 0) : x ≠ 0 := by` |
|  | `    x > 0` | `  exact ne_of_gt hx` |
|  | `    =>:` |  |
|  | `        x != 0` |  |
| **存在一个实数，其平方等于4；取2为见证** | `witness exist w R st {w^2 = 4} from 2` | `example : ∃ w : ℝ, w ^ 2 = 4 := by` |
|  |  | `  refine ⟨2, ?_⟩` |
|  |  | `  norm_num` |
| **由定义，3满足“超过二”的性质** | `prop is_above_two(t R):` | `def isAboveTwo (t : ℝ) : Prop := t > 2` |
|  | `    t > 2` |  |
|  |  | `example : isAboveTwo 3 := by` |
|  | `by def $is_above_two(3)` | `  norm_num [isAboveTwo]` |
| **直接检查一个算式** | `1 + 1 = 2` | `example : (1 : Nat) + 1 = 2 := by` |
|  |  | `  rfl` |
| **定义并调用非零实数上的倒数函数** | `have fn reciprocal(x R: x != 0) R = 1 / x` | `noncomputable def reciprocal (x : {y : ℝ // y ≠ 0}) : ℝ :=` |
|  | `reciprocal(2) = 1 / 2` | `  (x : ℝ)⁻¹` |
|  |  |  |
|  |  | `example : reciprocal ⟨2, by norm_num⟩ = (2 : ℝ)⁻¹ := by` |
|  |  | `  simp [reciprocal]` |
| **数系间的成员关系与表示** | `1 $in Z` | `example : ((1 : ℕ) : ℤ) = (1 : ℤ) := by simp` |
|  | `1 $in R` | `example : ((1 : ℝ) : ℂ) = (1 : ℂ) := by simp` |
|  | `1 $in C` |  |
| **定义集合，并检查一个成员** | `have multiples_of_four power_set(N) = {a N: a % 4 = 0}` | `def multiplesOfFour : Set ℕ := {a \| a % 4 = 0}` |
|  | `4 $in multiples_of_four` |  |
|  |  | `example : (4 : ℕ) ∈ multiplesOfFour := by` |
|  |  | `  simp [multiplesOfFour]` |

不只是Litex在语法上简单直白贴近自然的数学表达，Litex的验证效率在一些常见的数学问题上甚至达到了Lean的效率的10-100倍。这是因为Litex创新地提出了，以Lean为代表的其他形式化语言完全不同的软件架构和执行逻辑。

<!-- litex-lean-checking-table:start -->

<a id="litex-lean-checking-times"></a>

> 点击数学任务可查看附录中的完整 Litex 和 Lean 代码。定义类时间包含声明及随后使用，证明类包含完整证明。启动、依赖导入和结果输出均不计入。

| 数学任务 | Litex (ms) | Lean (ms) | Lean ÷ Litex |
| --- | ---: | ---: | ---: |
| [自然数算术：1 + 1 = 2](#litex-lean-code-nat_mathlib) | 0.037 | 1.361 | **36.7×** |
| [定义平方函数并计算](#litex-lean-code-expression_function) | 0.730 | 7.609 | **10.4×** |
| [定义开区间谓词并验证成员](#litex-lean-code-predicate) | 0.189 | 8.223 | **43.4×** |
| [按正负分段定义绝对值并计算](#litex-lean-code-piecewise_function) | 0.729 | 7.330 | **10.1×** |
| [二维点：声明、构造与字段访问](#litex-lean-code-structure) | 0.573 | 7.615 | **13.3×** |
| [定义并调用“正实数非零”定理](#litex-lean-code-named_theorem) | 0.158 | 8.018 | **50.7×** |
| [全称命题：两个正实数之和为正](#litex-lean-code-forall_add_pos) | 0.392 | 10.487 | **26.7×** |
| [集合论：正实数集合非空](#litex-lean-code-witness_nonempty_positive) | 0.084 | 6.439 | **76.9×** |
| [反证：不存在平方等于 −1 的实数](#litex-lean-code-contradiction) | 4.127 | 49.472 | **12.0×** |
| [归纳：前 n 个正整数求和公式（n≥1）](#litex-lean-code-induction_proof) | 43.626 | 174.986 | **4.0×** |
| [集合差的德摩根律](#litex-lean-code-set_de_morgan) | 0.425 | 2.991 | **7.0×** |
| [有限集合的子集数为 2ⁿ](#litex-lean-code-powerset_general) | 0.296 | 1.320 | **4.5×** |
| [使用 sum：1²＋⋯＋10²＝385](#litex-lean-code-sum_sq_10) | 2.224 | 8.266 | **3.7×** |
| [数论：1000000007 是素数](#litex-lean-code-prime_1000000007) | 0.027 | 4.029 | **147.2×** |
| [对数：log₂8 = 3](#litex-lean-code-log_2_8) | 0.064 | 13.992 | **217.0×** |
| [平方函数在 3 处的导数为 6](#litex-lean-code-derivative_square_at_three) | 1.464 | 29.945 | **20.5×** |

下面再沿着这些例子，解释Litex的设计思路。Litex希望让用户能让Litex源码能和想表达的数学一一对应上，同时还不失严格性。

## Litex的缘起

Litex围绕这样的想法展开：能不能写下数学，直接得到形式化代码？ 从小我们就知道数学是一种严格的语言，每一句话都能找到相应的佐证来支撑它的正确性。那既然数学本身就是一个严格的语言，为什么不能让数学本身成为一种形式化语言？或者设计一个形式化语言，它在书写上就和日常数学差不多，只是添加一些合理的约束就应该确保其足够结构化，方便去机械地做证明。

这里的观察是，自然语言数学里的许多日常表达，其实已经承担着精确的逻辑责任：

- “任取一个……”确定变量、范围和量词。
- “假设……”引入局部前提，并限定它的有效范围。
- “存在……使得……”要求提供见证，或者提供存在性依据。
- “由定义……”要求表达满足定义中的条件。
- “因此……”要求结论确实能从当前上下文推出。

能不能找到一套语法，让自然语言数学中的对象、条件和推理步骤，与形式化语言里的表达直接对应起来？能不能找到一套运行机制，不但能帮你验证，能让你恍然大悟：哦，我平时在做数学证明的时候，就是这么思考数学的，这个语言做证明的机制和我思考数学时的想法很相似？

> 形式化语言大大降低了数学家审稿的时间，但不代表它就是完美无缺的。因为现有形式化语言的语法和语义和标准数学相距很远，所以经常造成误解。对初学者而言，Lean的`1 / 0 = 0`, `1 - 2 = 0`这样的性质会让人非常困惑。就像C语言中的内存泄露，Lean的语义偏移也是非常难以察觉到的问题。参见[Faults in Our Formal Benchmarking: Dataset Defects and Evaluation Failures in Lean Theorem Proving](https://arxiv.org/html/2606.29493v1#A5)

Litex从第一性原理重新思考数学、自然语言与代码的关系。它想让数学本身成为一种形式化语言。我希望，任何使用数学的人，不论是中小学生还是AI工程师，只需学习少量语言约定，就能从已有的数学表达出发，使用形式化工具，并理解机器检查的依据。

## Litex的公理基础、语法、语义和软件架构

### Litex的数学公理基础

第一个问题是：选择合适的数学公理基础，并确定对象和运算的含义。Lean选择类型论，数学库也为具体运算选择了明确的约定。比如，Lean/Mathlib 把实数除法扩展为全函数，规定 `(1 : ℝ) / 0 = 0`；自然数减法在零处截断，因此 `(1 : Nat) - 2 = 0`（参见 [Division by zero in type theory: a FAQ](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)）。这些是具体编码与数学库的选择，类型论也可以表达受限定义域，Lean的整数减法同样满足 `1 - 2 = -1`。但熟悉的符号带着不同约定时，使用者需要额外确认：形式化陈述表达的，是否还是原来想说的数学。

为了让更多人学会并使用Litex，Litex选择集合论作为它的基础。集合、元素、函数与关系。这些写法是我们在中学就学过的，不会像Lean基于的类型论那样难懂。学习Litex的门槛不应该高于LaTeX，因为LaTeX里常见的数学对象Litex都有。在Litex，`1 / 0`是会因为不满足良定义性而报错，而`1 - 2 = -1`。

### Litex的语法

数学词汇就位之后，下一个问题是设计语法。我要让数学语言直接就成为形式化代码：写下对象、定义、条件和推理步骤，让它们在语言中承担相应的作用。

说“任取一个实数x，假设它大于零，那么它不等于零”，可以写成：

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

Litex的语句的基本的语法参考了Python，用缩进表示不同的层级。Litex中参数以及它的类型的语法是模仿Go语言的，比如这里的 `x R` 读作 `x是集合R中的元素`。`R`显然在Litex里表示实数集合。

定义一个非零实数上的倒数函数，并计算一个值，可以写成：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

这里也能逐段对应：`have fn reciprocal` 定义函数，`(x R: x != 0)` 指定参数是非零实数，后面的 `R` 指定值属于实数，`= 1 / x` 给出函数值。调用时，系统需要从当前上下文确认参数满足定义域条件；`reciprocal(0)` 就不能通过这个检查。

这两个例子展示了我希望保留的对应：数学对象、前提、定义域和推理步骤，在代码中各有明确的位置。这里追求的一一对应，是数学含义、推理动作与作用域的对应；普通数学中省略的条件和背景知识，仍需要通过明确的上下文或规则提供。

### Litex的语义

上面的例子说明怎样写；开头的第二个问题则是：系统怎样检查，并告诉我为什么成立？清晰的语法只是开始，运行机制还要把每句话与它的依据连起来。

当你输入`1 + 1 = 2`，选择中文输出（`-lang zh`），Litex会返回下面这样的单条语句结果。这里节选与解释有关的字段：

```json
{
  "语句判定": "accepted",
  "语句": "(1 + 1) = 2",
  "证明方法": {
    "类型": "封闭计算",
    "规则名": "封闭计算",
    "说明": "精确计算封闭表达式，不递归搜索证明"
  },
  "存储": [
    "(1 + 1) = 2"
  ],
  "推断": []
}
```

当你输入 `1 / 0 = 1 / 0`时，结果会指出没有满足的良定义条件，具体原因放在“错误列表”里。下面同样是中文输出的字段节选：

```json
{
  "运行结果": "failure",
  "语句结果": [
    {
      "语句判定": "rejected",
      "语句": "(1 / 0) = (1 / 0)"
    }
  ],
  "错误列表": [
    {
      "语句索引": 0,
      "语句": "(1 / 0) = (1 / 0)",
      "阶段": "良定性",
      "说明": "未能证明该语句中的表达式有定义。",
      "类别": "well_defined",
      "表达式": "(1 / 0)",
      "待证条件": "0 != 0"
    }
  ]
}
```

同样的过程也适用于前面的倒数函数。检查 `reciprocal(2) = 1 / 2` 时，参数需要满足 `2 != 0`，然后才能使用函数定义检查等式；换成 `reciprocal(0)`，就缺少定义域所要求的非零条件。检查存在性见证时，要确认见证属于指定集合并满足相应性质；检查 `by def $is_above_two(3)` 时，要确认定义中的 `3 > 2`。

我希望这些数学依据能被系统直接展示。上面的输出就说明，`1 + 1 = 2`由“封闭计算”这个规则检查出来；除以零的例子则指出无法满足的条件（Litex的输出涵盖中文、英文等10种语言，`accepted`、`rejected`等固定值保留英文）。用户写出数学对象与步骤，检查器返回找到的依据，或者指出当前缺少的条件与证明。结构化的验证记录还需要适合读者的呈现，才能成为清晰的教学解释。

> 更多信息：Litex的`litex -session`交互模式，像Python的REPL那样，语句失败了但还能保留已经接受的定义和事实。就像打草稿一样，写错了不要紧，只有做对的事情才会被保留下来成为后续输入的上下文。例如你已经接受了 `let a = 2`，接着试 `a = 3` 会失败，但同一 session 里仍可用刚才的 `a` 去验证 `a + 1 = 3`——失败的那一步丢掉，做对的上下文留下。常见的 Lean 文件工作流里，改一处往往还要再跑一遍相关检查；Litex 把“增量保留已接受事实”做成了默认体验。这样的交互方式非常适合Litex和AI Agent交互地批量化生成证明。

### Litex的软件架构

我希望Litex像身边的一个严格的老师：检查通过时，说明所用依据；没有通过时，指出当前无法证明的地方。找不到证明，并不等于这句话在数学上是错的。

这一选择塑造了验证引擎。在典型Lean的 tactic 工作流里，作者给出构造证明的指令，最终由内核检查。Litex 把“下一条数学事实”放在交互的中心：给定当前上下文，系统能否为这个陈述辩护？这是关于默认写作体验的选择：Lean 的文档说明了它自己的 [elaboration 与检查模型](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)，它默认用户写how to prove的tactic串，由Lean来告诉你what to prove；Litex默认用户写what to prove的证明过程，由Litex来告诉你how to prove的。

数学的常见对象非常非常多，语句也很多，但毕竟是有限的，Litex的一大贡献是，通过2年的不断摸索，把对象之间的常见关系，语句之间的常见关系，串联起来了，让日常的数学表达真的能几乎1比1被视作Litex语句了。每个常见的数学对象，有自己的定义，有自己的和其他对象的关系，这些都被做成600多个内置规则留在litex里了。用户不需要考虑这些很琐碎（trivial）的东西。

实现这"基于上下文找到对应的事实，用适当的规则来验证每一步"的基本逻辑很直观：匹配与代换。找到相关的已知事实，与正在检查的陈述做匹配，再判断所需的代换与条件是否成立。这个想法后来发展成：把数学事实的存储和证明，看成数学特化的SQL的存储和查找的逻辑。所有的数学语句，在Litex里都被视作一种键，这个键会去匹配到潜在的，可能可以被用来证明它的上下文和内置的规则。

例如，先写下两行：

```litex
let a = 1
a + 2 = 3
```

`let a = 1` 向上下文写入了一条记录：`a = 1`。随后，`a + 2 = 3` 成为一个查询键，引导系统寻找能够支持它的事实和规则。系统找到已知等式 `a = 1`，通过等式代换将目标化为 `1 + 2 = 3`，再由内置计算机制完成验证。验证成功后，`a + 2 = 3` 又成为上下文中的一条新记录，供后续的数学语句继续查询和使用。

Litex 会把验证记录输出为 JSON，说明它实际引用了哪些上下文事实，以及用了什么规则来证明。默认命令行直接打印验证摘要；详细 JSON 还保留具体的事实引用和逐层验证依据。下面是通过现有 Detailed 接口输出的这一示例的详细 JSON 节选，省略了良定义检查等字段：

```json
{
  "statement_result": "accepted",
  "statement": "(a + 2) = 3",
  "verify": {
    "fact": "(a + 2) = 3",
    "searched_proof": {
      "type": "by_builtin_rewrite",
      "rule": "ClosedNumericEqualSubstitution",
      "rewritten_left": "(1 + 2)",
      "rewritten_right": "3",
      "cited_equal_fact_ids": [
        {
          "fact_id": "f1",
          "fact": "a = 1"
        }
      ],
      "residual_equal": {
        "fact": "(1 + 2) = 3",
        "searched_proof": {
          "type": "by_closed_calculation",
          "kind": "equal",
          "values": {
            "representation": "decimal",
            "left_normal": "3",
            "right_normal": "3"
          }
        }
      }
    }
  },
  "store_and_infer": {
    "stores": [
      {
        "fact_id": "f2",
        "fact": "(a + 2) = 3"
      }
    ]
  }
}
```

这里，`cited_equal_fact_ids` 打印出找到并引用的上下文事实 `a = 1`；`rule` 指出使用了已知数值等式的代换规则 `ClosedNumericEqualSubstitution`。`residual_equal` 继续展示代换后的目标 `1 + 2 = 3`，以及通过 `by_closed_calculation` 精确计算两边都得到 `3` 的依据。最后，`stores` 记录新事实 `a + 2 = 3` 被存入上下文。这样的 JSON 把“查到了什么、用了什么规则、又建立了什么事实”直接展示出来。如果我找不到上下文，或者找不到对应的规则，就证明不出来。比如`b = 1`是`unknown`的，因为我不知道b是什么。

Lean 则将命题表示为类型，将证明展开为依赖类型理论中的证明项——可以理解为带有依赖类型的 λ 演算表达式——再由内核检查这个证明项是否具有待证命题对应的类型。换句话说，在 Lean 中，证明一个命题，就是构造一个具有相应类型的项，并通过类型检查。[Lean 官方说明](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html)。

> Litex之所以在某些场景下可能比Lean快很多，从数学上看，是因为Litex始终在同一个抽象层上验证，不会太跨抽象层。从软件架构看，Lean 所说的“内核很小”，指的是检查器采用的基本规则少、实现比较精简。Lean 需要生成相应的证明项，把这些重写及其组合表达出来。因此，用户只写一行 tactic，背后的证明项却可能很长。例如，[Lean 4.30 的发布说明](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/)提到，先前某些短字符串比较会迫使内核执行 UTF-8 编解码和字节数组比较，触发 86 次以上的展开，后来通过改变证明生成方式进行了优化。这种机制意味着，表面简短的数学推理，可能对应Lean的体积很大的证明项，或者触发代价很高的类型检查与归约计算。当然，一定有一些场景里，Litex比Lean慢。只是说正因为实现架构截然不同，二者有足够多的差异性。

总之，为了把这些表达、上下文与验证依据连在一起，我自行开发了Litex的数学特化数据库和搜索引擎。现在，这个流程不只是能做验证，还能输出结果，告诉你为什么这些数学语句能成立。所有的结构化信息连起来，就成了一张网，帮助读者理解数学概念之间怎样互相连接。这个过程可能会改变读者对数学、代码与证明的看法。

![Litex verification pipeline](https://litexlang.com/assets/diagrams/litex-verification-pipeline-v2.png)

## Litex 编译到 Lean

litex能把常见的数学表达一步步解析成机器可识别可存储可调用的数学知识，是很难的，这个功能是Litex项目的核心，也是Litex多达20多万行Rust源代码的内核所做的。这也让我想到数学教育：我们可以构建可交互的数学书，数学书以接近自然数学表达的Litex源码出现，每句经过验证的语句都能对应一份“为什么成立”的结构化信息。

用一个年龄小例子把这条链摊开：同一份推理，依次落成 Litex 源码、说明依据的 JSON、以及 `-lean` 生成的 Lean（当前为预览编译；下表 Lean 列为真实输出的节选）。

| Litex 源码 | JSON（中文验证结果摘要） | Lean（`-lean` 节选） |
| --- | --- | --- |
| `let my_age = 3` | `{` | `noncomputable def _object_i1 :=` |
| `let brother_age = 3 * my_age` | `  "语句判定": "accepted",` | `  Litex.number (M := M) (3 : ℂ)` |
| `brother_age = 3 * 3 = 9` | `  "语句": "brother_age = (3 * 3) = 9",` |  |
|  | `  "证明方法": {` | `theorem h_1 :` |
|  | `    "类型": "复合事实",` | `  Litex.Same (_object_i1 …)` |
|  | `    "规则名": "链式"` | `    (Litex.number … (3 : ℂ)) := …` |
|  | `  },` |  |
|  | `  "存储": [` | `-- … 中间略 …` |
|  | `    "brother_age = (3 * 3) = 9",` |  |
|  | `    "brother_age = (3 * 3)",` | `theorem h_470 :` |
|  | `    "(3 * 3) = 9"` | `  Litex.Same (_object_i2 …)` |
|  | `  ]` | `    (Litex.number … (9 : ℂ)) := …` |
|  | `}` |  |

Litex 源码是人写的数学；JSON 记录机器存下来的“为什么成立”；Lean 代码是同一结果接到 Lean 后的证明形态。可交互数学书可以使用这些验证记录；需要独立复核时，再检查生成的 Lean 证明。

以上编译之所以是可能的，是因为Litex基于集合论，而Lean基于类型论。因为类型论能表达集合论，所以，Litex的任何对象和语句都能对应到若干Lean代码。同时，Litex的验证机制的每一步都是很简明的，比如`代入`，`计算`，`三段论`，而这些都能对应到若干个Lean的tactic的组合。所以不论是Litex要证明的语句，还是Litex的验证过程，都能对应到Lean代码。

同一份记录也为通往 Lean 的桥梁提供了基础。Litex 有自己的语言和验证机制。在当前编译器支持的范围内，可以结合源码和验证记录，按 Litex 实际使用的推理生成 Lean 陈述与证明，再交给 Lean 内核独立检查。这让我们在 Litex 给出的检查结果之外，多了一条复核途径。Litex能编译到Lean有巨大价值。它给 Litex 一条进入 Lean 生态的路径，并为翻译后的证明增加一层独立检查。Lean一直以难以被阅读著称，它的语义和标准数学语义也有一些冲突。Litex相当于提供了门槛更低的，让普通人使用形式化工具的一种途径：熟悉的表层与快速检查在 Litex；更深的库与独立内核复核可以接到 Lean。更完整的并排例子见[Lean–Litex 示例对比](Lean与Litex示例对比.md)。

因为Litex的内核运行机制和Lean本质不同，所以Litex在某些最基本的任务上的效率可能远远高于Lean。所以像Litex这样探索数学的基础这样的工作是有意义的，至少能能大家以全新视角看待这一个数学问题，即如何将数学高效代码化。

## 总结

虽然做数学研究的评价体系受到了AI冲击，但我觉得现在是学习数学的最好的时候（相关讨论见 3Blue1Brown 的[《There's never been a better time to go into math》](https://www.youtube.com/watch?v=LKrwhjOI8Nc)）。普通人不需要做数学，他们只需要使用数学，把数学当做他们理解世界的工具。AI并没有促进人们理解数学，它在帮人学习数学上还只是一种电子化的做题家老师。但Litex不同。Litex从第一性原理上，重新审视了什么是数学，什么是推理这样的问题。希望学习过Litex的读者，未来看到自然语言写的数学，也能联想到Litex，联想到数学本身也是一个严格的语言，它有它背后的逻辑和脉络。我想就够了。

Litex 仍在快速开发中。欢迎大家使用并提出宝贵建议。想要了解litex怎么工作的，可以联系litexlang@outlook.com。

附录：

## Litex在AI上的实际表现：以建数学库、解IMO题为例

初步的实验结果表明，**Litex 的运行机制适合 AI Agent 持续进行“生成—验证—纠错—积累”的交互工作。**Litex在构建Lean/Mathlib尚未覆盖的数学知识上的效率很高。[Litex–Lean 平面几何库自动构建实验](https://github.com/litexlang/Litex-VS-Lean-AutoBuild)对此进行了初步探索：让 AI 分别使用 Litex 和 Lean 自动构建几何库，生成的代码交给各自的验证器检查，再根据错误反馈修改。

实验共设置 **165 项定理证明任务**，涵盖向量、距离、直线、圆、平行、垂直等概念及相关性质。仓库公布的汇总结果如下：

| 实验阶段 | 比较指标 | Litex | Lean |
|---|---|---:|---:|
| 定理证明：165 项任务 | 成功率 | **90.8%** | **70%** |
| 定理证明：165 项任务 | 总耗时 | **280.8 分钟** | **638.9 分钟** |

我们对实验结果的初步探索表明，Litex输出的JSON结果对AI找到错误、纠正错误起到了关键的辅助作用。这也是Litex比Lean总耗时少非常多的原因，因为Litex试错更快。

**Litex 的另一个特点是对大型既有数学库的依赖很低。**本实验的 Litex 没有导入外部数学库，而是利用原生的Litex为用户提供的功能，从实数坐标、点积和行列式逐步搭建几何概念。

| 特性 | Litex | Lean |
|---|---|---|
| 标准库 | 无（从零构建） | Mathlib（约 300 MB） |
| 实数运算 | 手动定义 | 现成（Real 类型） |
| 几何库 | 完全自建 | 部分现成 |



## Litex和Lean设计和实现上的比较

**1. Lean 的数学对象、要证明的命题，以及证明，都统一放在类型论的框架里。命题是类型，证明是这个类型的项。这让这个语言很强大、很通用，但是对于学习者来说，也容易困惑。Litex 的对象和事实是分开的。**

举例，Lean 里：

```text
a : ℝ       a 是一个实数
P : Prop    P 是一个命题
h : P       h 是 P 的证明
```

这里的对象、命题、证明，都是用“某个东西属于某个类型”的方式表达。

Litex 里：

```litex
have a R = 2
a + 1 = 3
```

第一句引入对象，第二句说关于这个对象的事实。对象是对象，事实是事实。

`a + 1` 是对象表达式，还没有说什么成立。不能直接在Litex里输入它，因为这句话没有在判断对错

`a + 1 = 3` 是事实表达式，说了一个需要检查的事情。

**2. Litex 主要的源码证明流程是自下而上的，从条件出发，积累中间步骤，最后达到结果。积累的过程可以是每句话紧紧依赖前一句话，也可以依赖更前面的某句话。因此阅读 Litex 像是从第一页到最后一页地看教科书；Lean 常见的目标驱动式写法更像是自上而下的，从结果出发，不断改变当前要证明的目标，阅读的时候要跟着这些目标的变化。因此阅读这种 Lean 证明，有点像从最后一页往第一页看教科书。**

这里不是说 Lean 一定只能自上而下。Lean 也有 `have` 和 `calc`，可以从条件往后写。这里说的是这两种写法给人的通感。

举例，已知：

```text
P
P 能推出 Q
Q 能推出 R
```

从条件出发，就是：

```text
P 成立，所以 Q 成立，所以 R 成立。
```

从目标出发，就是：

```text
要证明 R，只需要证明 Q。
要证明 Q，只需要证明 P。
P 已知，结束。
```

再举一个计算的例子：

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = (-4)
```

就是先消元，得到 `y`，再代回去得到 `x`。最后一句既用到前一句，也用到最开始的条件。读的时候能直接顺着数学过程往下看。

3. 图灵奖得主 Dijkstra 的重要贡献之一，就是推动了[结构化编程（structured programming）](https://www.cs.utexas.edu/~EWD/transcriptions/EWD02xx/EWD249/EWD249.html)。顺序、分支、循环这些基本结构，让人不用跟着一堆跳转去理解程序。它们足够通用，也足够直白，让人能把代码和自己想表达的事情对应起来。

Python 也可以从这个角度理解。用户不用自己处理对象的[内存分配和释放](https://docs.python.org/3/c-api/memory.html)，很多底层细节都帮用户封装好了。这些事情仍然要做，只是交给 Python 的实现来完成。Python 替用户做的越多，它内部需要承担的工作也就越多。

Litex 本质上也在做类似的事情：找到数学语言里常见的表达和推理模式，把它们组织成内置的 `obj`、`fact`、`stmt`，再把常见的证明步骤和组合方式做成几百条内置规则。

**从实现上，Lean 表达很多数学概念的时候，会用到一层又一层的类型、结构和类型类。Litex 走的路线不一样。Litex 直接默认一批足够常见的数学概念、数学语句的存在，内置它们之间的关系和性质，用户在这些东西上继续做数学。**

如果Lean用户想理解Litex的工作原理，可以这样思考，Litex就是找到了那几百种最常见的tactic的组合方式，把它们做成了内置规则，又发明了一套数学特化的数据库提取和查找系统，让你每次输入一个事实的时候，我系统都会找到相应的内置规则，找到相应的上下文，来试图证明这个事实。正是把常见规则内置了，有了搜上下文潜在的证明前提的能力，Litex才能让`1 + 1 = 2`这样看似简单，实则其他形式化语言不能作为合法语句直接写出来的语句合法，才可以让`1/0=0`, `1 - 2= 0`这样"Lean当中奇怪的事实"不出现。

上下文和证明规则的区别：

```litex
let a = 2
a + 1 = 3
```

这里 `a = 2` 是 `a + 1 = 3` 的上下文；“把 `a` 的值代入，并发现 `2 + 1` 确实等于 `3`”是证明规则。上下文来自你的 Litex 源码；规则内置在 Litex 里。Litex 内置了几百条常用规则，这些规则单拿出来都让人觉得很熟悉，但找到它们、实现它们、让它们和谐工作，工作量很大，这也是 Litex 的“苦劳”。

对应到 Lean，如果上下文里已经有 `h : a = 2`，目标是 `a + 1 = 3`，最接近的写法是：

```lean
subst a
norm_num
```

或者：

```lean
rw [h]
norm_num
```

其中 `subst` / `rw` 负责把值代进去，`norm_num` 负责算出两边确实相等。关键差别在于：Lean 里你通常要指出用哪条假设 `h`、选哪个 tactic；Litex 的内置规则会自动在当前上下文中找到对应的等式 `a = 2`，选中“等式改写 + 封闭计算”这条路线，再把 `a + 1 = 3` 检查通过。也就是说，Litex 不仅内置了规则，还内置了“在上下文里找到合适前提 `h`”的检索能力。用户只写要证明的事实，系统负责找到那条能让它通过的上下文事实。

不管是把Litex视作Lean的一个大前端语言（甚至是可以视作一个巨大的宏或者一个巨大的tactic），还是把Litex视作独立的形式化语言，我相信都是有价值的。总之可以说，在所有ai都在追求前沿数学，把前沿数学问题当benchmark刷时，litex是一个重新思考数学底层基础的工作从我们最熟悉的经验出发，让人类和机器说同一种数学语言。


<!-- litex-lean-checking-code-appendix:start -->

## 附录：16 个计时例子的完整代码

编号与[计时表](#litex-lean-checking-times)的顺序一致。每个例子单独运行；不同例子的定义和定理名称可能重复，不应直接拼接为同一个程序。Lean 代码中的 `import Mathlib` 在计时前完成，导入耗时不在主表内。

这些是 2026-10-22 至 23 日在同一台 macOS arm64 工作机上的多批本地观测，工具为 Litex 1.1.2-beta release 和 Lean/Mathlib 4.31.0。

Litex 计时包含词法、解析、良定义性、验证执行和存储，新 Runtime 的创建在计时外；Lean 包含命令 elaboration、证明构造或声明生成及同步内核检查，命令解析在计时外。各项在三个进程中重复采样：Litex 共 90 或 300 个暖样本，Lean 共 21、93 或 303 个；首次检查另记，不混入中位数。工作机没有隔离 CPU 或受控清空缓存。

<a id="litex-lean-code-nat_mathlib"></a>

### 1. 自然数算术：1 + 1 = 2

Litex：

```litex
1 + 1 = 2
```

Lean：

```lean
import Mathlib

example : (1 : Nat) + 1 = 2 := by rfl
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-expression_function"></a>

### 2. 定义平方函数并计算

Litex：

```litex
have fn bench_square(x R) R=x^2
bench_square(3)=9
```

Lean：

```lean
import Mathlib

def bench_square (x : Real) : Real := x^2
theorem bench_use : bench_square 3 = 9 := by norm_num [bench_square]
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-predicate"></a>

### 3. 定义开区间谓词并验证成员

Litex：

```litex
prop bench_in_open(x,a,b R):
    a<x
    x<b
by def $bench_in_open(1,0,2)
```

Lean：

```lean
import Mathlib

def bench_in_open (x a b : Real) : Prop := a < x ∧ x < b
theorem bench_use : bench_in_open 1 0 2 := by norm_num [bench_in_open]
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-piecewise_function"></a>

### 4. 按正负分段定义绝对值并计算

Litex：

```litex
have fn bench_abs(x R) R by cases:
    case x>=0: x
    case x<0: -x
bench_abs(-3)=3
```

Lean：

```lean
import Mathlib

noncomputable def bench_abs (x : Real) : Real := if 0 ≤ x then x else -x
theorem bench_use : bench_abs (-3) = 3 := by norm_num [bench_abs]
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-structure"></a>

### 5. 二维点：声明、构造与字段访问

Litex：

```litex
struct BenchPoint:
    x R
    y R
have bench_point &BenchPoint=(1,2)
bench_point.x=1
```

Lean：

```lean
import Mathlib

structure BenchPoint where
  x : Real
  y : Real
def bench_point : BenchPoint := ⟨1,2⟩
theorem bench_use : bench_point.x = 1 := by rfl
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-named_theorem"></a>

### 6. 定义并调用“正实数非零”定理

Litex：

```litex
thm bench_positive_is_nonzero:
    ? forall x R:
        x>0
        =>:
            x!=0
release thm bench_positive_is_nonzero(3)
```

Lean：

```lean
import Mathlib

theorem bench_positive_is_nonzero : ∀ x : Real, 0 < x → x ≠ 0 := by
  intro x hx
  exact ne_of_gt hx
theorem bench_use : (3 : Real) ≠ 0 := bench_positive_is_nonzero 3 (by norm_num)
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-forall_add_pos"></a>

### 7. 全称命题：两个正实数之和为正

Litex：

```litex
forall x,y R:
    x > 0
    y > 0
    =>:
        x+y > 0
```

Lean：

```lean
import Mathlib

theorem bench : ∀ x y : Real, 0 < x → 0 < y → 0 < x+y := fun x y hx hy => add_pos hx hy
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-witness_nonempty_positive"></a>

### 8. 集合论：正实数集合非空

Litex：

```litex
witness $is_nonempty_set({x R:x>0}) from 1
```

Lean：

```lean
import Mathlib

example : Set.Nonempty {x : Real | 0 < x} := ⟨(1 : Real), (show (0 : Real) < 1 from zero_lt_one)⟩
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-contradiction"></a>

### 9. 反证：不存在平方等于 −1 的实数

Litex：

```litex
by contra:
    ? not exist x R st {x^2=-1}
    obtain root from exist x R st {x^2=-1}
    root^2>=0
    root^2=-1<0
    impossible root^2>=0
```

Lean：

```lean
import Mathlib

theorem bench_use : ¬ ∃ x : Real, x^2 = -1 := by
  by_contra h
  obtain ⟨x,hx⟩ := h
  nlinarith [sq_nonneg x]
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-induction_proof"></a>

### 10. 归纳：前 n 个正整数求和公式（n≥1）

Litex：

```litex
have fn bench_terms(k Z) Z=k
by induc n from 1:
    ? 2*sum(1,n,bench_terms)=n*(n+1)
    ? from n=1:
        sum(1,1,bench_terms)=bench_terms(1)=1
    ? induc:
        bench_terms(n+1)=n+1
        sum(1,n+1,bench_terms)=sum(1,n,bench_terms)+bench_terms(n+1)
        2*sum(1,n+1,bench_terms)=2*(sum(1,n,bench_terms)+(n+1))=2*sum(1,n,bench_terms)+2*(n+1)=n*(n+1)+2*(n+1)=(n+1)*(n+2)
```

Lean：

```lean
import Mathlib

def bench_terms (k : Int) : Int := k
theorem bench_use : ∀ n : Nat, 1 ≤ n → 2 * (∑ k ∈ Finset.range n, bench_terms ((k+1 : Nat) : Int)) = (n : Int) * ((n : Int)+1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [bench_terms]
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    simp only [bench_terms] at *
    push_cast at *
    nlinarith
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-set_de_morgan"></a>

### 11. 集合差的德摩根律

Litex：

```litex
forall A,B,D power_set(R):
    set_minus(A,union(B,D))=intersect(set_minus(A,B),set_minus(A,D))
```

Lean：

```lean
import Mathlib

theorem bench : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := fun A B D => sdiff_sup
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-powerset_general"></a>

### 12. 有限集合的子集数为 2ⁿ

Litex：

```litex
forall A finite_set:
    A $subset N
    =>:
        finite_set_size(power_set(A))=2^finite_set_size(A)
```

Lean：

```lean
import Mathlib

theorem bench : ∀ A : Finset Nat, A.powerset.card = 2 ^ A.card := by intro A; exact Finset.card_powerset A
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-sum_sq_10"></a>

### 13. 使用 sum：1²＋⋯＋10²＝385

Litex：

```litex
sum(1, 10, fn(k Z) Z {k^2}) = 385
```

Lean：

```lean
import Mathlib

theorem bench : Finset.sum (Finset.range 10) (fun k => (((k + 1 : Nat) : Int)^2)) = 385 := by decide
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-prime_1000000007"></a>

### 14. 数论：1000000007 是素数

Litex：

```litex
$prime(1000000007)
```

Lean：

```lean
import Mathlib

example : Nat.Prime 1000000007 := by native_decide
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-log_2_8"></a>

### 15. 对数：log₂8 = 3

Litex：

```litex
log(2,8)=3
```

Lean：

```lean
import Mathlib

example : Real.logb 2 8=3 := by
  rw [show (8:Real)=2^3 by norm_num, Real.logb_pow]
  rw [Real.logb_self_eq_one (by norm_num : (1:Real)<2)]
  norm_num
```

[返回计时表](#litex-lean-checking-times)

<a id="litex-lean-code-derivative_square_at_three"></a>

### 16. 平方函数在 3 处的导数为 6

Litex：

```litex
$has_derivative_at(fn(t R) R {t^2},3,6)
```

Lean：

```lean
import Mathlib

theorem bench : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by have h := hasDerivAt_pow 2 (3 : Real); norm_num at h; exact h
```

[返回计时表](#litex-lean-checking-times)

<!-- litex-lean-checking-code-appendix:end -->
