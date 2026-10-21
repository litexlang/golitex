# Litex 蓝图：让数学本身成为形式化代码

**Write math, get formalized code: because the math already is.**

_写下数学，得到形式化代码：因为写下的数学本身就是代码。_

从小我们就知道，数学是一种严格的语言，每一句话都需要成立的依据。**既然数学本身已经如此严格，能不能让我们日常书写的数学，直接成为形式化代码？** Litex 围绕这个问题展开：保留熟悉的数学表达，加上明确的语法和合理的约束，让机器能够检查它。

这是我从第一性原理重新思考数学、自然语言与代码之间关系的尝试。我想构建一门语言，让人直接写下数学对象、定义和推理步骤，就能使用形式化工具，并读懂自己写下的内容。选择什么数学基础、怎样设计语法、怎样寻找成立依据、怎样解释验证过程，都是从这个想法一步步长出来的问题。

Litex 仍在快速开发中。这份蓝图沿着这条设计思路，展开当前的语言、验证器与工具，以及我希望继续探索的方向。

**读音：** Litex 读作 /ˈliːtɛk/（“里泰克”），不是“赖泰克”。

文档由沈嘉辰创建和维护。

最后更新：2026 年 10 月 21 日。

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint

## 目录

- [0. 从数学到可检查的语言](#overview)
  - [0.1 Litex 的目标](#goal-of-litex)
  - [0.2 六大特点，同一个语言设计](#overview-spine)
- [1. 熟悉的表达，应当保留熟悉的数学含义](#ordinary-mathematics)
- [2. 写下事实，看到成立的依据](#fact-oriented)
  - [2.1 事实导向：把“什么成立”写进源码](#fact-oriented-interface)
  - [2.2 每句话都留下什么：可检查知识记录](#execution-model)
- [3. 从熟悉的数学公理和符号开始：Litex 的集合论基础](#set-theory)
  - [3.1 设计难处：把具体的数学写法做成工作语言](#design-difficulty)
- [4. 让形式化融入数学工作流](#mathematical-workflow)
  - [4.1 每一步，都留下可以继续使用的知识](#workflow-principle)
  - [4.2 边想边写，边写边检查](#workflow-exploration)
  - [4.3 把今天的成果，留给下一次探索](#workflow-reuse)
  - [4.4 让数学成果用于计算与交流](#workflow-use)
- [5. Litex 适合与 AI 交互](#interaction-loop)
- [6. 连接 Lean 独立复核，并与 Mathlib 兼容（Experimental）](#compatibility)
- [7. 从验证记录继续构建](#ecosystem-role)
- [8. 追寻与众不同的艺术](#conclusions)
  - [Litex 的数学价值观](#mathematical-values)
  - [特别感谢](#special-thanks)
- [附录：几个语言设计问题](#overview-readers)
  - [人怎样阅读和审阅已检查的证明](#reader-mathematicians)
  - [个人思考：目标引导与事实积累](#summary-bottom-up-and-top-down)
- [附录：从系统工程的角度看 Litex](#systems-engineering)
- [附录：源码速览（gallery）](#overview-gallery)
- [项目主张、实际交付与检查证据](#claims-deliverables-evidence)

<a id="overview"></a>

## 0. 从数学到可检查的语言

_“语言是人类理性的工具，而不只是表达思想的媒介。”_

_— George Boole，《思维的规律》（1854），第 II 章（节选）_

要让数学本身成为形式化语言，第一个问题是：选择什么数学基础，对象和运算应该有什么含义？我选择集合论，用集合、元素、函数与关系组织数学。熟悉的符号也应带着明确的含义和使用条件：`1 - 2 = -1`，而 `1 / 0` 因为没有定义而被拒绝。

数学词汇就位以后，接下来是语法。写下 `1 + 1 = 2`，这句数学本身就是要检查的源码；量词、前提和结论也按数学思路组织。复杂论证由作者给出构造和中间步骤，语言检查这些步骤之间受支持的衔接。

这样的语法，又决定了验证器需要回答的问题：给定当前上下文，这条数学陈述凭什么成立？我从匹配与代换开始，逐步构建了事实查找、条件检查、内置规则和显式证明步骤。存储与查找像一个专为数学推理设计的数据库，需要理解数学结构、作用域，以及事实在什么条件下可用。

我还希望检查器解释自己的工作。源码写下数学，输出说明检查用了什么方法、建立了什么事实，以及失败停在哪里。语法、语义和输出需要一起设计，让人既能看懂自己说了什么，也能检视系统为什么接受它。

有了源码和验证记录，知识复用、AI 逐步修正证明、交互式数学工具和 Lean 编译才有了继续构建的基础。这些可能性沿着同一条语言设计路线展开，具体支持范围在后文分别说明。

*Litex 始于 2024 年，由沈嘉辰创建和维护。*

<a id="goal-of-litex"></a>

### 0.1 Litex 的目标

**让熟悉的数学对象、事实和语句，直接成为代码。**

人选择数学想法、定义和证明路线，写出有意义的步骤；执行器记住数学上下文、检查使用条件、寻找局部依据，并记录结果。它的存储与查找需要按数学结构、作用域和事实的适用条件组织。

倒数带着非零条件，简单等式直接写成等式，一条定义成为下一条陈述可使用的知识。为了让作者这样写，执行器里需要完成相应的工作。这就是 Litex 正在探索的分工，语法和受支持的检查也仍在发展。Litex 文本本身就是形式化源码；受支持的 Lean 编译进一步利用这份源码和验证证据。

我希望，使用数学的人也能更自然地使用形式化工具，理解、检查并继续构建自己写下的数学。下面六大特点，展开支撑这个目标的具体设计。

<a id="overview-spine"></a>

### 0.2 六大特点，同一个语言设计

前三项展开语言本身：数学含义、陈述方式与数学对象；后三项展开这种语言怎样积累知识、支持交互，并连接其他工具。它们共同回答：写下的数学怎样成为可检查、可继续使用的源码？

| 特点 | 对数学写作意味着什么 |
| --- | --- |
| **1. 熟悉的数学含义与定义域** | `1 - 2 = -1`；使用除法必须满足分母非零。[含义与定义域](#ordinary-mathematics)。 |
| **2. 直接写数学事实** | 写下 `1 + 1 = 2`，语言检查这条事实并解释依据。[事实导向](#fact-oriented)。 |
| **3. 熟悉的对象、公理与符号** | 用成员关系、条件和熟悉的符号定义集合、函数与关系。[数学对象](#set-theory)。 |
| **4. 连贯的数学工作流** | 探索、定义、证明、复用，并把受支持的成果用于计算或 LaTeX 排版。[数学工作流](#mathematical-workflow)。 |
| **5. 通过明确反馈与 AI 协作** | 提出步骤、检查结果，在保留已接受知识的同时修复失败步骤。[人–AI 交互](#interaction-loop)。 |
| **6. 独立 Lean 复核与生态互通** | 将受支持的证明路线编译到 Lean，并通过已审阅接口连接 Mathlib。[Lean 连接（实验性）](#compatibility)。 |

后文章节按这个顺序展开。[验证流程图](https://litexlang.com/assets/diagrams/litex-verification-pipeline-v1.png)展示一条事实如何被检查，并扩展后续可用的上下文。

<a id="ordinary-mathematics"></a>

## 1. 熟悉的表达，应当保留熟悉的数学含义

要让数学书写直接成为代码，首先要把它的含义规定清楚。证明可以通过检查，但熟悉的符号可能表达了作者没有预期到的含义。导入 Mathlib 后，下面这些 Lean 陈述都能得到证明：

```lean
import Mathlib

example : (1 : ℝ) / 0 = 0 := by simp
example : (1 : Nat) - 2 = 0 := by rfl
example : (1 : Int) - 2 = -1 := by rfl
example : Real.sqrt (-1) = 0 := by
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)
```

对于期待通常整数减法的读者，两行减法把问题直接摆在眼前：改变类型，就改变了减号的含义。除法和平方根的两行则在通常实数运算没有定义的地方赋予了数值。作者必须先理解这些选择，才能判断已经通过检查的公式是否表达了自己的原意。

**Litex 把熟悉的数学含义和定义域条件作为起点。** 减法保留通常的整数结果：

```litex
1 - 2 = -1
1 - 2 $in Z
```

对于有定义域限制的运算，条件直接进入定义：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

第一行读作：“对非零实数 `x`，把它的倒数定义为 `1 / x`。”调用时必须满足这个条件。`reciprocal(0) = 0` 会在良定义性检查处被拒绝，`1 / 0 = 0` 和 `sqrt(-1) = 0` 也是如此。即使写成 `1 / 0 = 1 / 0`，两边相同也不能使除法有定义。

这些选择针对的是默认数学表达中的具体差异。Lean 也能编码受限定义域，其约分定理仍保留必要的假设；Litex 则直接在作者使用的源码表达式上检查定义域。作者负责选择符合原意的定义和定理陈述，语言检查受支持的条件与证明步骤。

表达式保留了作者想要的含义之后，下一步就是怎样陈述事实本身。这引出了第二大特点：**写下数学陈述，由语言检查受支持的成立依据。**

<a id="fact-oriented"></a>

## 2. 写下事实，看到成立的依据

_“可读性很重要。”_

_— Tim Peters，《Python 之禅》（PEP 20）_

**数学陈述本身，就是交给检查器的源码。** 要陈述一加一等于二，直接写下这条事实：

```litex
1 + 1 = 2
```

同一算术事实的一种简短 Lean 证明是：

```lean
example : (1 : Nat) + 1 = 2 := by rfl
```

Litex 把普通事实本身作为检查入口：作者直接写等式，无需为这条计算套上 `example` 声明，也无需选择证明命令。更难的论证仍需要作者给出构造与有意义的中间步骤，Litex 检查受支持的局部连接。

同样的原则可以从一个算式延伸到一句数学陈述。“对任意实数 `x`，若 `x > 0`，则 `x + 1 > 1`”可以写成：

```litex
forall x R:
    x > 0
    =>:
        x + 1 > 1
```

纸面顺序就是思考顺序：引入任意实数，写出假设，再写结论。`=>:` 前的条件是局部假设，后面的结论必须通过检查。

<a id="fact-oriented-interface"></a>

### 2.1 事实导向：把“什么成立”写进源码

作者写下接下来应当成立的事实，Litex 就开始检查：先确认表达式是否良定义，再从内置规则与策略、已知事实、全称事实和定义中寻找局部依据。许多常见步骤的验证方法由语言选择和组合；关键构造、见证和估计仍由作者给出。

#### Litex如何帮用户按事实形状寻找验证路径

原子目标具有可识别的关系或谓词形状，例如 `>=`、`$is_positive`、`$in`。验证器据此检索候选，实例化参数或沿已知等式对齐写法，再核对前提；没有受支持的路径就停在目标处。这是有边界的局部查找，不是无限制的证明搜索。形状索引有助于控制候选范围；速度和内存效果仍须在可比任务上测量。 已存 forall 的等式结论还按两侧的嵌套构造、函数位置和参数空位检索。固定子项先使用已有的 Direct 等式，再沿受支持的构造下降；实例化后的载体与前提仍须验证。

常见匹配对象有四类：

| 匹配什么 | 内核做什么 | 极小例子 |
| --- | --- | --- |
| **内置规则与策略**（builtin） | 按谓词/参数形状筛选路径，在允许的范围内组合检查前提 | 已知 `x >= 0`、`y >= 0`，匹配“非负之和仍非负”，得到 `x + y >= 0` |
| **已知具体事实** | 在上下文中找到同形事实；必要时用等式对齐写法 | 已知 `$is_positive(a)` 与 `a = b`，匹配并替换得到 `$is_positive(b)` |
| **已知 `forall`** | 把目标形状对上全称事实，实例化参数并检查前提 | 已有 `forall x R: x > 1 => $is_positive(x)`，且 `b > 1`，匹配得到 `$is_positive(b)` |
| **定义**（def） | 把具名谓词与其定义体互相同形状匹配 | 已知 `a > 0`，匹配 `prop is_positive` 的定义，得到 `$is_positive(a)` |

```litex
prop is_positive(a R):
    a > 0

# 1) 匹配内置规则（builtin）
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y

# 2) 匹配已知事实，再用等式替换
forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)

# 3) 匹配已知 forall（先存下这条全称；再由 b > 1 得到 $is_positive(b)）
forall x R:
    x > 1
    =>:
        x > 0
        $is_positive(x)

have b R:
    b > 1

$is_positive(b)

# 4) 匹配 prop is_positive 的定义
have a R:
    a > 0

$is_positive(a)
```

第一段中的 `0 <= x + y` 没有点名验证工具。Litex 根据加法与序关系选择候选路径，再检查当前上下文中的 `0 <= x`、`0 <= y` 等前提。形状匹配只是找到候选；所需前提也通过检查，才能接受结论。后三段展示同一默认流程如何复用已知事实、实例化全称事实和使用定义。

固定恒等式 `tan(x)*cot(x)=1` 先由等式良定义检查实数参数，以及实际的
`sin(x)!=0`、`cos(x)!=0` 证据，再匹配同一个角度。`TanCotProduct` 叶子
不另开前提搜索；Detailed 同时保留它与外层良定义的真实引用。
`TanSquareReciprocalCosine` 对应 `1+tan(x)^2=1/cos(x)^2`，需要
`cos(x)!=0`。这两条固定规律没有恢复一般三角展开器。

负或非正公共因子的反序规则分两步：验证因子符号，再验证反向的参数序。
四种比较、四种乘法位置各有独立证据，共16个叶子。固定的反写或更强
前提候选沿用调用权限，并保留实际验证结果；没有新增全局规范化或搜索
阶段，既有正/非负路线仍优先。严格不等式的反序不能使用零因子。

第一象限规则读取实际的严格条件 `0<x<pi/2`，保留两个来源引用。两条
非零规则供正切、余切既有的良定义检查消费；四个独立的 Less/Greater
叶子在良定义之后证明正性。没有新增搜索阶段或持久状态。

固定区间检查接受负半圆周端点的四种字面写法及比较的两个方向，保留实际
验证的条件。已存数字等式的替换沿原标量表达式遍历：先匹配整个已知值，
再处理子项；处理子项后形成的父表达式也可匹配已知值。选中的等式都有
真实引用，剩余目标沿用既有权限，表项顺序不会决定原子项是否仍可匹配。
搜索阶段与持久状态保持原合同。

| 作者的数学工作 | Litex 的常规验证工作 |
| --- | --- |
| 选择定义、构造对象并给出条件 | 检查对象、参数范围和良定义条件 |
| 写出本步要建立的事实 | 按事实形状检索已知依据、规则和组合策略 |
| 给出中间等式、见证或局部推导 | 检查各步所需前提，记录结果并复用已验证事实 |
| 选择证明的数学路线 | 控制默认搜索的调用权限和改写范围 |

Litex 的设计特点在于把这些能力组织为同一种日常使用方式：以数学对象和事实的分类为基础，普通事实自动触发局部验证，通过后继续扩展可用知识。作者在支持范围内可以直接写数学步骤，语言实现承担其中许多机械验证操作。

当前实现以 `VerifyState` 给查找路径分级：直接证据、已知对象性质、内置规则、策略、定义与全称事实依次拥有不同权限。规则检查前提时只把更低的查找权限传下去；定义或全称事实的改写在同一分支上也有明确的使用边界。这样，增加规则不仅是加入一个结论，还须说明它能调用哪些前提、如何避免反复调用自身。用户仍只需写出本步要建立的事实。

<details>
<summary><strong>哪些步骤 Litex 自动检查，哪些需要作者写出来？</strong></summary>

平面零向量例子 (`examples/proof_nodes/equal/by_builtin_rule/add_zero_from_equalities.lit`)
直接检查 `plane_add((0,0),x)=(x(1),x(2))=x`，无需另写零向量的坐标值。
每个加法保留“一个加数等于零”和“另一加数等于目标”的证明；函数定义域
和坐标索引仍须通过检查，这条局部路线不会重新开启通用 rewrite 搜索。

作者选择定义、构造和关键中间结论；Litex 从当前知识中检查受支持的局部步骤。边界取决于这一步需要做什么：是沿固定结构检查已有依据，还是需要选择尚未给出的证明路线。不能简单按“自动推几步”划分。

**沿统一结构检查类型。** 下面的表达式有多层加法，但作者不必为每层加法单独补一个类型事实：

```litex
have n N
((n+1)+1)+1 $in N
```

Litex 沿受支持的加法结构使用自然数的闭包性质。这不意味着任意运算都保持自然数类型；定义域和运算条件仍要成立。

**给出中间等式，再复用结果。** 作者可以把定义到数值的路线写出来：

```litex
have x R = 2
have y R = x + 1
y = x + 1 = 3
y^2 = 9
```

第三行指明先展开 `y`，再计算 `x+1`。链检查通过后，端点等式 `y=3` 已成为可用事实，第四行不必重写这条推导。

**给出递归展开路线。** 对一个自己定义的函数，作者可以指出使用哪条递归方程、代入哪个已经建立的值：

```litex
have fn f(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: f(n - 1) + 1
f(0) = 0
f(1 - 1) = f(0) = 0
f(1) = f(1 - 1) + 1 = 0 + 1 = 1
```

这里 `f` 的值来自作者给出的定义。最后的链依次使用递归方程、初值和算术；在同样的定义与 `f(0)=0` 下，直接写 `f(1)=1` 在当前验收中没有自动闭合。显式路线可检查，不要求默认搜索自行发现所有递归展开组合。

搜索可以做得更强，但增加搜索分支也会增加运行和维护成本。Litex 希望自动承担有明确结构、证据和成本边界的机械推理，让作者写出有意义的数学步骤。反复补机械类型或重复已有证据时，应检查系统是否缺少统一支持；不能把所有失败都归给作者。这个取舍的效果仍须通过实际任务测量。

</details>

<a id="automation-implementation"></a>

<details>
<summary><strong>为什么 Litex 的验证内核需要这么多实现？</strong></summary>

作者省去的操作仍然需要完成。为了直接检查上面的 `0 <= x + y`，系统需要识别目标形状，选出候选路径，检查对象与两个非负前提，记录验证依据，并让结论成为可复用的事实。这些职责转移到了语言实现中。

**分类与组合。** Litex 内置了大量常见数学规则与受限组合策略，覆盖的对象、运算和关系各有适用条件。按数学类别细分路径，有助于缩小候选范围，也让每种组合可以有明确的前提与调用边界。本文用“规则与组合策略”描述这些实现；它们不必对应其他证明助手中同名的 tactic。

**前提与证据。** 除了匹配目标，系统还要检查参数所属集合、函数调用条件以及所需事实，保存结果并向作者反馈。这些检查使作者能够省去常规操作，也使每条验证路径都需要相应实现。上面的类型检查、等式链和递归例子展示了不同路径的分工。

**搜索与维护成本。** 让系统继续寻找中间结论、尝试更多改写或递归展开，需要更多搜索分支和组合处理。默认流程因此有明确权限：对给出的局部步骤寻找依据，在支持边界处由作者补充数学路线。反复出现的机械衔接仍应检查是否缺少通用支持。每条新增路径都需要审查数学条件、证据和成本，代码规模本身不能替代这些审查。

这里的“验证内核”指项目中的验证与执行实现，包含依据搜索、内置数学规则、良定义检查、事实存储和反馈。[Lean 的语言参考](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)将精化与 tactic 执行和检查核心证明项的可信内核分开；比较代码规模时需要区分这些职责。当前验证依赖 Litex 验证器及其内置规则、推理规则的正确性；[第 6 节](#compatibility)说明独立 Lean 复核的目标与现状。

</details>

<details>
<summary><strong>当前有多少对象、语句与内置验证路径？（2026-10-04 快照）</strong></summary>

以下按源码提交 `2ecde77d0` 的 Rust 枚举清点。各行的单位不同，不能相加为一个“内置定理总数”。

| 实现层 | 数量 | 统计单位 |
| --- | ---: | --- |
| `Obj` | 17 大类；展开后 91 种形状 | 对象与表达式的 AST 分类 |
| `Stmt` | 9 大类；展开后 50 种形状 | 事实、定义、证明命令等语句的 AST 分类；其中 `ByStmt` 有 10 种，`ReleaseAndExpandStmt` 有 7 种 |
| `Fact` / `AtomicFact` | 10 / 46 | 事实形状 / 原子关系形状 |
| 内置规则（builtin rule） | **551** | 非空的末级证明结果分支：等式 267、其他原子事实 259、析取 16、存在式 9 |
| 内置策略（builtin strategy） | **128** | 策略结果分支：等式 8、其他原子事实 120 |
| 内置改写 / 内置谓词定义路径 | 6 / 11 | 分别统计的结果分支，不并入上面的规则数 |
| 保留的具名内置定理 | 29 | 可由通用 `release thm` 等入口调用的不同定理名 |

这里的“展开”也有固定边界：`Obj` 展开直接的数学表达式家族，保留名称、函数调用和模板实例三个通用入口；`Stmt` 展开一级语句家族及其 `DefineObjStmt`，不继续展开其中的 `Fact`。因此 91 和 50 是语法形状数，不是 91 个内置数学对象或 50 条定理。

这些规则分支围绕具体的数学接口组织，并非随意增加的证明招式。每个被计数的分支都有具名的证明结果形状，面向对象运算、事实或语句的逻辑结构，或常见数学性质；它不一定是对某条源码定义的直接展开。上面的 `0 <= x + y` 同时涉及加法对象与 `<=` 事实；对应的 `SumOfNonnegatives` 结果分别保存两个非负前提的验证依据。`UnionCommutative` 对应集合并的常见性质，`EqualityWitnessFromMembership` 则把已知成员事实用于存在式的见证。每类路径都有目标形状和适用条件，策略在规定权限内组合检查；这正是较简洁的用户写法背后需要的实现工作。数字反映这些接口及证据分支的结构规模，不证明每个分支都已在当前版本中可触达、正确或获得 Lean 独立复核；这些仍须逐路径审查。

</details>

<details>
<summary><strong>为什么 Litex 能维护事实表？Lean 能否扩充实现同一机制？</strong></summary>

Lean 可以扩展自动化；`simp` 与 `grind` 已经会利用已知事实。Litex 的选择更具体：把按事实形状进行受限局部检查作为普通语句的默认行为，同时把命题接口限制在更易索引的范围内。例如，它不支持 `forall p prop` 这样把任意命题作为量化对象的写法；通常面对的是具名谓词与成员、等式、序关系等原子目标。

这个限制使 Litex 当前的事实表与规则表能够按关系或谓词头缩小候选，再检查参数和前提。它不是证明 Lean 无法实现相近体验，也不是说一旦允许高阶命题就无法索引任何目标；它说明 Litex 为默认检查路径选择了怎样的表达边界。由此得到的易用性与失去的表达方式，都应在实际形式化任务中检验。

</details>

下面再用三组 Lean–Litex 对照，把其中几类匹配展开成完整界面对比。Lean 源码当然也包含陈述目标的 theorem statement，Litex 也允许显式指定定理和证明结构；差异在默认的注意力中心：

| 典型界面 | 源码主要呈现 | 交互输出主要呈现 |
| --- | --- | --- |
| Lean tactic proof | theorem statement 给出目标，tactic proof body 主要写 **how**：怎样改写、应用定理或关闭目标 | Infoview 显示 **what**：当前还需要证明什么 |
| Litex 事实导向证明 | 源码主要写 **what**：哪些对象、条件和事实应当成立 | 验证输出解释 **how**：事实因何被接受，或验证停在哪里 |

这张表比较的是典型工作流，不是两种语言全部书写方式的界限。下面三组代码展示不同依据的来源；日常 Normal JSON 只概括顶层方法，更细的前提检查保存在详细验证结果中。

<details>
<summary><strong>例子 1：Lean 与 Litex 如何验证“两个非负实数之和仍然非负”</strong></summary>

**内置规则与策略。** Litex 把目标拆成谓词与参数形状，据此筛选候选路径，再检查类型、前提和条件是否全部成立。

要证明的数学事实是：两个非负实数之和仍然非负。

**Lean 源码｜proof body 写 how**

```lean
import Mathlib

example (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : x + y ≥ 0 := by
  exact add_nonneg hx hy
```

最后一行明确告诉 Lean 使用 `add_nonneg hx hy` 关闭目标。执行这一行之前，Infoview 显示的是尚待证明的 **what**：

**Lean Infoview｜显示 what**

```text
x y : ℝ
hx : x ≥ 0
hy : y ≥ 0
⊢ x + y ≥ 0
```

**Litex 源码｜直接写 what**

```litex
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y
```

这条源码没有指定规则名称。目标 `0 <= x + y` 可拆成谓词 `>=` 与参数 `x + y`、`0`；内核据此筛选候选，匹配出两个非负前提，并继续检查类型和条件。

当前 CLI 的 Normal 输出将整条 `forall` 标为 `compound_fact`，并存下该全称事实；它不在这个顶层摘要里逐条展开内部的规则检查。

</details>

<details>
<summary><strong>例子 2：Lean 与 Litex 如何复用一条全称事实</strong></summary>

**用户提供的全称事实。** 已证明的 `forall` 事实会进入上下文；遇到同形目标时，Litex 匹配参数并检查实例化后的前提。 整条来源复用也会对齐嵌套 `forall` 前提和 `exist!` witness 中的绑定变量；完整载体、条件和自由对象身份必须保持，WD 仍按调用者原权限检查。这是结构比较，不增加搜索路线。验证记录保留实际存储事实的引用。

第二个数学事实是：若实数 `a > 10`，则存在一个正实数严格小于 `a`。前面建立的全称事实随后可直接用于具体的 `a`。

**Lean 源码｜proof body 写 how**

```lean
import Mathlib

def HasPositiveWitness (n : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ n > a

theorem hasPositiveWitness_of_gt_ten (x : ℝ) (hx : x > 10) :
    HasPositiveWitness x := by
  refine ⟨10, by norm_num, ?_⟩
  exact hx

example (a : ℝ) (ha : a > 10) : HasPositiveWitness a := by
  exact hasPositiveWitness_of_gt_ten a ha
```

最后一行执行前，Infoview 给出当前 **what**；源码中的 `exact` 指定完成它的 **how**：

**Lean Infoview｜显示 what**

```text
a : ℝ
ha : a > 10
⊢ HasPositiveWitness a
```

**Litex 源码｜直接写 what**

```litex
prop is_positive(n R):
    exist a R+ st {n > a}

claim:
    ? forall x R:
        x > 10
        =>:
            $is_positive(x)
    witness exist a R+ st {x > a} from 10

have a R:
    a > 10

$is_positive(a)
```

这里 `prop` 给出可复用接口；`claim` 建立一条可实例化的全称事实。后面的 `have` 提供具体前提，最终源码只写 `$is_positive(a)`，没有再次写出怎样调用全称事实。

这段源码在当前 CLI 中通过；最后一句的 Normal 输出记录 `proof_method.type = cite_forall`，并将 `$is_positive(a)` 加入 `stores`，说明这一步使用了已知的全称事实。

</details>

<details>
<summary><strong>例子 3：Lean 与 Litex 如何沿等式运输一个具体事实</strong></summary>

**具体事实与已知等式。** Litex 也能从上下文中的具体事实出发，利用已知等式对齐写法不同但相等的参数。

第三个数学事实是：已知 `a` 为正且 `a = b`，推出 `b` 为正。这里需要借助等式把一个具体事实运输到另一个写法。

**Lean 源码｜proof body 写 how**

```lean
import Mathlib

def IsPositive (x : ℝ) : Prop :=
  x > 0

example (a b : ℝ) (ha : IsPositive a) (hab : a = b) : IsPositive b := by
  simpa [hab] using ha
```

执行 `simpa [hab] using ha` 之前，Infoview 只呈现当前 **what**：

**Lean Infoview｜显示 what**

```text
a b : ℝ
ha : IsPositive a
hab : a = b
⊢ IsPositive b
```

**Litex 源码｜直接写 what**

```litex
prop is_positive(x R):
    x > 0

forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)
```

Litex 源码保存前提和结论，没有写 `simpa` 或指定等式改写方向。验证器从上下文找到 `$is_positive(a)`，再利用 `a = b` 对齐参数。

当前 CLI 接受并存下这条全称事实；Normal 输出将顶层方法概括为 `compound_fact`，具体的等式替换步骤需要查看内部验证结果。

</details>

<details>
<summary><strong>个人观察：命令式与声明式编程的类比</strong></summary>

Lean tactic 证明与 Litex 事实导向写法的命令式／声明式类比，放在文末[写给程序员](#reader-programmers)一节展开。

</details>

<details>
<summary><strong>设计空间中的位置：寻找局部证明依据并非 Litex 独有</strong></summary>

[Lean `grind`](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)、
[Rocq `auto`](https://rocq-prover.org/doc/master/refman/proofs/automatic-tactics/auto.html)
和 [Isabelle/Isar](https://isabelle.in.tum.de/doc/isar-ref.pdf) 通过显式证明指令（tactic）或
证明方法（proof method）提供局部自动化；[Mizar](https://mizar.uwb.edu.pl/project/mizman.pdf)
有空验证（empty justification）；
[ACL2](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFTHM) 可以在没有提示（hints）时
尝试证明定理事件（theorem event）；[Naproche](https://naproche.github.io/) 则用自动定理证明器
检查受控自然语言中的步骤。Litex 更具体地检验：普通数学陈述能否触发受当前上下文和规则限制的局部验证，并在通过后写回上下文、显示验证来源。

局部自动化可以建立在不同的逻辑基础上。Litex 的研究问题是：在受限的命题接口、集合论式对象和逐句积累的上下文中，让普通陈述默认触发可解释的局部检查，能否降低书写与审阅成本。与这些系统的成本比较仍须用具体任务检验。

</details>

**多语言反馈。** 同一份源码可以得到英文、中文或其他受支持输出语言的 JSON 说明。当前语言代码为 `en`、`zh`、`zh-hant`、`fr`、`ru`、`es`、`ar`、`ja`、`ko` 和 `vi`。语言设置改变反馈，不改变被检查的数学。下一节说明这些记录保留什么。

<a id="execution-model"></a>

### 2.2 每句话都留下什么：可检查知识记录

每条通过验证的语句都为后面的证明增加可用的知识。执行结果记录本步的顶层依据、存入的事实和适用范围内的推断；失败时则指出停止位置。读者把源码和结果放在一起，就能看见这一步如何成立、又留下了什么。更完整的验证证据保留在内部结果树中，供详细工具和 Lean 编译器使用。

先看一个最小的连续片段：

```litex
let a = 1
a + 1 = 2
```

第一句是定义（`define`）：它引入对象，并把定义事实 `a = 1` 存入上下文。第二句是验证（`verify`）：它读取当前上下文，检查 `a + 1 = 2` 的良定义性，再利用 `a` 的已知值通过内置改写验证等式。通过后，第二条事实进入当前上下文，成为后续语句可以继续使用的基础。

下面的 Normal JSON 摘录记录了这两条语句及其实际采用的证明路径。

<details>
<summary><strong>展开查看：Litex执行结果</strong></summary>

```json
{
  "kind": "run",
  "run_result": "success",
  "target": "eval",
  "path": null,
  "detail": "normal",
  "session_terminated": false, "termination": null,
  "statement_results": [
    {
      "statement_result": "accepted",
      "statement": "let a = 1",
      "proof_method": { "type": "define_obj" },
      "stores": ["a = 1"],
      "infers": []
    },
    {
      "statement_result": "accepted",
      "statement": "a + 1 = 2",
      "proof_method": {
        "type": "builtin_rewrite",
        "rule_name": "Builtin rewrite",
        "message": "Verified by a builtin equality rewrite"
      },
      "stores": ["a + 1 = 2"],
      "infers": []
    }
  ]
}
```

</details>

第二句通过良定义性检查，并采用内置等式改写。上面的 Normal JSON 摘录把这条实际路径记录为 `builtin_rewrite`，并未展开每个内部子步骤。读者可从这份日常记录直接回答几个问题：

| 读者想知道什么 | 在记录里看哪里 |
| --- | --- |
| 跑了哪一句 | `statement` |
| 是否成功 | 语句的 `statement_result`，以及整次运行的 `run_result` / `session_terminated` / `termination` |
| 为什么成立 | `proof_method`（规则名、引用、定义路径等） |
| 为什么停下 | `why_failed.phase` 与 `why_failed.goal` |
| 什么进入了后续上下文 | `stores` 与 `infers` |

Normal JSON 是面向人与工具的摘要，日常 `-e` / `-f` / `-r` 不会打印完整的 verify/exec 证据树。[Lean 编译器](#compatibility)直接读取内部结果，将受支持的验证路径翻译成 Lean 证明。

良定义性先于事实接受：`1 / 0 = 1 / 0` 即使两边形式相同，也因分母为零而不能成为已接受的等式。

<details>
<summary><strong>展开查看：Litex执行结果</strong></summary>

当我们输入 `1 = 0` 时，Litex 的 Normal JSON 输出是

```json
{
  "kind": "run",
  "run_result": "failure",
  "target": "eval",
  "path": null,
  "detail": "normal",
  "session_terminated": false, "termination": null,
  "statement_results": [
    {
      "statement_result": "rejected",
      "statement": "1 = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "1 = 0"
      },
      "stores": [],
      "infers": []
    }
  ]
}
```

失败语句不会把 `stores` 或 `infers` 加入已接受上下文；外部的写作工具可以保存这次尝试和反馈，供人或 AI 修复。Litex 返回诊断，并不自动替用户维护完整的尝试档案。

</details>

上例中，结果记录显示 `a + 1 = 2` 用到了定义 `a = 1`、定义化简和数值计算；这个等式随后成为可引用的事实。Normal JSON 给出摘要，Detailed JSON 则展开前提和事实引用。读者可以据此[追溯证明中的联系](#reader-mathematicians)，工具也可以把这些关系画成图。第 5 节介绍怎样在[交互中使用反馈](#interaction-loop)，第 6 节介绍 [Lean 独立复核](#compatibility)。

![Litex 事实关系图示例](https://litexlang.com/_next/image?url=%2Fassets%2Fknowledge_graph.png&w=640&q=75)


<details>
<summary><strong>实现摘要：记录如何生成</strong></summary>

语句执行后会留下结构化结果，供输出工具和 Lean 编译器使用：

```text
Litex 源码
  → 解析为带类型的对象和语句
  → 执行定义或验证
  → 检查良定义性、形状、依据和前提
  → 生成结构化执行结果
  → 提交候选或回滚候选
  → 更新已接受上下文，并在适用时运行推断
  → 让用户和人工智能看见已接受路径、上下文变化和修复边界
  → 为工具和交互式视图保留可检查知识记录
  → 在需要时提供 JSON 和关系图等机器可读或结构化视图
  → 按需将支持范围内的结果编译为 Lean，再单独运行 Lean 检查
```

JSON 和关系图呈现内部执行结果。Lean 编译器读取受支持的结果并生成证明；生成文件还需交给 Lean 检查。

</details>

<a id="set-theory"></a>

## 3. 从熟悉的数学公理和符号开始：Litex 的集合论基础

_“语言设计，是宏大思想与繁琐细节的一种奇妙混合。”_

_— Bjarne Stroustrup_

Litex 以集合论为数学基础，用集合、元素、函数和关系组织数学。源码可以直接写下成员关系、子集关系、函数应用和等式，无须先展开常见对象的具体集合论构造。这种写法的目标，是让读者沿用熟悉的数学概念，降低理解形式化表示的额外成本。内置规则和数系接口如何对应基础理论，仍须逐项说明和审查。

事实需要讨论的对象。第三大特点把同样的数学阅读顺序延伸到函数和集合的定义。

“定义到原点的距离；`-3` 和 `3` 到原点一样远”可以写成：

```litex
have fn distance_from_zero(x R) R = |x|
distance_from_zero(-3) = distance_from_zero(3) = 3
```

“把所有正实数收集成一个集合；二属于这个集合”可以写成：

```litex
have positive_reals set = {x R: x > 0}
2 $in positive_reals
```

`forall`、`have fn` 和集合描述式，为熟悉的数学语句提供精确形式。Litex 使用有明确规则的形式语法；这里贴近自然语言的是数学思路与源码之间的对应，并不表示系统能够理解任意自然语言段落。

例如，若 `s` 包含在 `t` 中，那么二者分别与同一集合 `u` 取交集后，前者仍包含在后者中：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

**数学符号输入。** 同一个结论也可以输入为 `s ∩ u ⊆ t ∩ u`。Litex 接受 `∩` 与 `⊆`，并将它们规范化为 `intersect` 与 `$subset`。文中多数例子采用英文字母拼写，只是因为普通键盘输入更方便。

可以看到，这样的写法和我们在日常数学中看到的集合论陈述非常接近。

下面是《Mathematics in Lean》集合论章节中的同一数学语句的 Lean 版本：

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

Lean 先声明共同元素类型 `α : Type*`，再声明 `s`、`t`、`u : Set α`。这让定理可在任意元素类型上复用；`Type*` 还涉及类型的宇宙层级。

这里比较的是两种语言怎样引入集合并展开证明：Lean 先声明集合的元素类型，Litex 直接写下并检查集合之间的事实。Lean 同样可以用短证明或自动化完成这个结论；这里保留教材的展开步骤，方便读者对照。

> **集合论是数学基础；日常书写可以从熟悉的概念开始。**

这里有两个常见问题：是否要先熟悉集合论，以及是否要从 ZFC 公理开始构造每个对象。

<details>
<summary><strong>两层误解：不是“先学会集合论写法”，也不是“从 ZFC 从头砌砖”</strong></summary>

**误解 1：我不太熟集合论，就不会用∈、∪去表达群、拓扑空间、开集这类常见概念。**  
日常数学中的概念需要有对应的可读写法。群、拓扑空间及其开集族，都可以从它们的数学性质开始定义：

```litex
# Group: carrier set, operation, identity, inverse, and the usual laws
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

# Topology: a space is its carrier together with a family of open sets
prop is_topological_space(X set, open_sets power_set(power_set(X))):
    {} $in open_sets
    X $in open_sets
    forall U, V open_sets:
        intersect(U, V) $in open_sets
    forall family power_set(power_set(X)):
        family $subset open_sets
        =>:
            family_union(family) $in open_sets
```

开集就是该族中的成员：在显式假设 `$is_topological_space(X, open_sets)` 下，写 `U open_sets` 即表示 `U` 开。下文还有群与 Lean 的对照；这里只说明「词典」长什么样。覆盖仍在扩展，不宣称已经穷尽一切常用概念。

**误解 2：既然基础是集合论，是不是每次都要从 ZFC 公理把分析、代数、拓扑重造一遍？那会不会太难？**  
日常使用可以从已有的对象与结构开始，利用它们的性质继续证明，无须每次都展开具体的集合论构造。研究数学基础或某种具体构造时，Litex 也提供集合论／ZFC 一侧的公理与构造接口。作者可以根据问题，选择需要展开到哪一层。

更准确地说：Litex 的内置层关心的是对象、语句与事实之间**可检查的关系**，而不是选定某一种“真正的”具体构造定义。例如有理数 `Q`、实数 `R` 可以有多种集合论构造，函数也可以用不同的图编码来建模；内置接口不把其中某一种定为唯一定义，而直接给出成员、包含、函数定义域与值域行为等可操作的关系。需要某一种具体构造时，可以在源码中自行写出，或在必要时用 `trust` 标注兼容性假设。

因此，读者可以从群、拓扑空间等熟悉的概念开始，也可以在需要时使用基础公理接口。上面的片段和下文的群对照展示前一种写法；它们不要求读者先完成一套从空集公理开始的构造。

</details>

<details>
<summary><strong>技术总结：类型判断与成员事实</strong></summary>

Lean 把数学组织成有类型的项：经过细化后，核心表达式由 `Γ ⊢ e : T` 形式的判断检查。冒号属于元语言层的类型判断，不是 Lean 对象语言中可与等式、序关系或定理事实并列累积的普通命题。表层重载和强制转换可以把相似写法细化成不同的核心项，但每个所得项都在一个确定类型下接受检查。

Litex 则把数学组织成对象与逐步增长的事实上下文。`e $in S` 是对象语言中的成员事实，与等式、序关系和其他谓词处于同一逻辑层。因此，同一对象可被证明属于多个无关或相互重叠的集合：成员关系是对象之间的关系，不是唯一内生赋值 `typeOf(e) = S`。

对象能力的查找读取已检查的声明和为该确切对象建立索引的事实。函数调用检查需要签名；验证具体函数值还需要函数体。在 `have fn f(x R) R = x + 1` 后仅写 `let g = f`，不会转移该可调用契约：`g(4) = 5` 在良定义性阶段失败。显式包装 `have fn g(x R) R = f(x)` 提供自己的已检查签名和函数体，支持 `g(4) = 5`。仅有成员事实 `g $in fn(x R) R` 提供可调用性，并不确定具体函数值。建立索引的事实与相等传递的区别见函数接口细节 (`Litex手册.md`)。

这不等于取消静态约束或推断。Litex 在接受表达式前仍会检查定义域、返回集合、结构字段和其他良定义性义务，并通过专用规则在证明中推出成员与载体事实。区别在于，这种推断向上下文增加 `e $in S` 一类事实，而不是推断一个决定对象身份的特权类型 `e : T`。

Lean 以依赖类型论为核心；Litex 选择以集合与成员事实组织用户层数学。Lean 的 `Set α` 同样能表达集合论，Mathlib 也提供丰富的数学接口；差异在于两者默认让作者怎样引入对象、陈述事实和交代验证依据。Litex 当前的覆盖仍在扩展，不能由共同的数学目标推出两者现有的表达范围相同。Litex 的验证器与内置规则构成自己的可信实现面，因此把证据交给 Lean 独立复核很重要。初始的独立文件编译器已经回放有限范围内的当前验证结果，整个系统尚未覆盖。

</details>

<a id="design-difficulty"></a>

### 3.1 设计难处：把具体的数学写法做成工作语言

“更具体”说的是作者通常直接使用的数学词汇。[Lean 的语言参考](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)说明，Lean 表层语法精化为核心类型论表达式，并由内核检查证明；可执行程序的编译器 IR 是另一条路径。Lean 也有丰富的记号与自动化。Litex 则选择用集合、成员事实和具名函数组织日常书写。

例如，`have a R = 2` 看起来只是一句话，当前 CLI 却分别记录 `a $in R` 与 `a = 2`，供后面的良定义性检查、计算和等式对齐使用。一个对象可有多个成员事实，别名还会影响函数签名的查找。作者少写一步操作，语言就必须替他维护这些跨语句关系，并在接受下一句前检查它们是否足以支持该句。

设计的难点在于让数值计算、集合构造、函数、关系、量词、见证、反证与归纳协同工作。康托尔证明中的 `{x X: not x $in f(x)}` 同时涉及受限集合构造、函数应用、否定与成员关系。每一种组合都要回答：表达式何时良定义、可以引用哪些前提、如何控制重复搜索、成功后存入什么事实与依据、失败时停在哪里。当前验证器给规则前提逐级降低查找权限；执行语句时先在临时环境检查，失败不把候选事实合并进上下文。这些机制共同支撑了较简洁的写法。

Litex 把关键构造、中间结论和见证交给作者，并提供 `claim`、`witness`、`by contra`、归纳等显式结构。验证器负责检查这些步骤涉及的定义域、前提和事实引用。源码通过 Litex 检查后，其中受支持的路线还可以[编译到 Lean](#compatibility)接受独立复核。

<a id="group-comparison"></a>

<details>
<summary><strong>小例子：同一数学对象在不同的公理体系下的定义</strong></summary>

当标准库未覆盖某个领域时，用户能否从少量共同概念搭建理论？集合、函数、关系和运算是跨领域共享语言，可让定义和定理沿自身数学依赖生长，而非先服从外部库的编码。这就是**数学理论的自举**。

成熟库当然能加速建设，但不应成为表达新领域的前置边界。下面两个群片段表达同一结构和单位元唯一性，却呈现不同的载体、运算与规律接口。

群由元素、二元运算、单位元和逆元组成，并满足结合律、单位律和逆元规律。若另一元素也对所有元素表现为单位元，它必与原单位元相同。

#### Lean：`Type` 上的记录类型（record）与柯里化函数

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

Lean 用 `Carrier : Type` 指定元素类型，后面的运算和规律都依赖它。`Carrier → Carrier → Carrier` 是依次接收两个元素的柯里化二元函数；结合律和单位律则成为 `mul_assoc`、`one_mul` 等具名字段。这便于抽象和大型库复用，作者也须知道证明中调用哪个字段、等式朝哪个方向使用。上例显式调用了 `G.one_mul`。

#### Litex：集合上的运算与直接写下的结构事实

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

Litex 先绑定非空集合 `s`，再把群写成其上的结构。`mul fn(x, y s) s` 表示运算接收 `s` 中两个元素，结果仍在 `s` 中；群规律作为普通事实写在 `<=>:` 下。单位元唯一性随后直接写成等式链，由内核寻找单位律依据。长期使用的结果仍可命名为 `thm`，但局部事实不必都先变成需要记忆的接口。

`G.mul` 等字段路径按声明的结构载体检查，路径本身不会把群公理加入上下文。直接绑定 `G &Group<s>` 自动打开一层。结构定义还会发布带原参数和实例的全称性质，把结论中的内层全称变量合并到顶部，并保留前提与存在见证的依赖。普通全称事实匹配在验证实际载体和条件后可使用这些性质。`release struct def expression` 仍用于验证归属后显式释放一层表示与性质；单独的成员事实不会自动展开整个对象。

Lean 也能在不使用 Mathlib 的情况下自行定义群。这组例子比较的是日常写法；Litex 仍依赖验证器、规则和标准库，外部库也能帮助作者更快地建立理论。上文关于集合论基础与日常写法的区分，同样适用于这里的群例子。

群只是小示范。更强的检验是：小团队能否为现有库覆盖不足的领域建立可读、可扩展且边界清楚的接口。未来几何等领域库应以带日期的源码、验证结果、`trust` 边界和真实复用说明进展，而非预先宣称成功。

</details>

<details>
<summary><strong>设计空间中的位置：集合论式的表述并非 Litex 首创</strong></summary>

[Mizar 的数学库](https://wiki.mizar.org/library/) 基于塔斯基–格罗滕迪克（Tarski–Grothendieck）集合论；
[Lean](https://lean-lang.org/doc/reference/latest/The-Type-System/) 和
[Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/index.html) 向用户展示依赖类型论内核；
[Isabelle/HOL](https://isabelle.in.tum.de/website-Isabelle2024/dist/library/Doc/Isar_Ref/HOL_Specific.html)
使用多态高阶逻辑。

Litex 面向用户的命题语言大体具有一阶逻辑风格：原子关系或具名谓词通过受限的经典逻辑形式和量词组织。它偏好规范事实形态，命题和证明不能作为普通一等值任意组合——因此也不允许 `forall p prop` 一类对命题的量化；第 2 节说明这如何使事实表能按谓词名索引。这只描述命题接口；验证器还会检查良定义性，并从定义、上下文和受支持规则中寻找依据。

在这个背景下，Litex 的问题更具体地落在面向用户的对象接口上：
一套小型、以成员关系为中心的集合论式表层，能否在不要求用户先管理类型
宇宙（universe）的前提下，覆盖有实质内容的数学？

</details>

<a id="mathematical-workflow"></a>

## 4. 让形式化融入数学工作流

_“如果我看得更远，那是因为我站在巨人的肩上。”_

_— Isaac Newton，致 Robert Hooke 的信（1676）_

做数学时，我们会在定义、例子与证明之间往返。一个计算引出猜想，一次检查让条件变得清楚，一个证明又为下一个问题留下可用的结论。Litex 希望让这些动作在形式化中自然衔接。

以牛顿法逼近 √2 的单步更新为例。我们先探索它，再保存一个已经证明的性质，最后看看这份数学成果怎样用于计算与交流。

<a id="workflow-principle"></a>
<a id="bottom-up"></a>

### 4.1 每一步，都留下可以继续使用的知识

支撑这条工作流的是一个贯穿 Litex 设计的原则：**每条已接受的数学语句，都应在自己的作用域内为后续工作留下可用的知识。**

定义建立对象与词汇，证明积累已接受的事实。我们从已有的条件向前推进，每一个成立的中间结论都为下一步增加可用的依据。只要相应语句已经被接受，即使整体问题尚未解决，这些中间成果也可以继续使用。

REPL 中已接受的上下文、文件与模块中的定义和定理，都服务于这种积累。依赖记录帮助读者回看它们的联系；代码抽取与排版转换则为已有成果提供进一步的用途。

<a id="two-directions"></a>

<details>
<summary><strong>小例子：同一条代数等式的自上而下与自下而上写法</strong></summary>

Lean 的典型 tactic 交互先给出目标，再把它化为子目标。这里比较的是写作与交互的默认方向：Litex 常问“已知事实还支持什么”，Lean tactic 常问“当前目标还需什么”；两者都须严格检查所得结论。

这个例子展示同一等式的两种推进方向。Lean 从目标出发，每条 `rw` 指定事实、匹配方向和替换：

```lean
-- Using facts from the local context.
example (a b c d g f : ℝ) (h : a * b = c * d) (h' : g = f) :
    a * (b * g) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

Litex 从 `a * (b * g)` 写出等式链，逐步到达 `c * (d * f)`。当前内核可验证这个由左向右的方向：

```litex
claim:
    ?forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    a * (b * g) = (a * b) * g = (c * d) * g = (c * d) * f = c * (d * f)
```

四个等号依次使用乘法结合、`a * b = c * d`、`g = f` 和再次结合。Lean 指定下一步如何改写目标；Litex 写出沿途应当成立的事实，再由内核寻找相邻等式的依据。

</details>

<details>
<summary><strong>设计空间中的位置：前向证明并非 Litex 首创</strong></summary>

Mizar、Isar、ACL2 和 Naproche 已支持前向文本、定理累积或逐步检查，因此“自下而上”并非 Litex 独有。Litex 检验的是组合：普通事实自动触发局部验证，通过后扩展上下文，同时让已接受或停下来的路径保持可见，供用户或人工智能检查和修复；只有常规验证不足时才写显式证明结构。更完整的比较见第 2 节的小结“Litex 与 Naproche——相近目标，不同核心接口”。

</details>

<a id="workflow-exploration"></a>

### 4.2 边想边写，边写边检查

从一个正数 `x` 出发，更新公式是 `(x + 2 / x) / 2`。这里的“正数”有实际作用：它保证除法有意义，也让更新后的数仍然为正。先检查这件事，再定义函数：

```litex
claim:
    ? forall x R+:
        (x + 2 / x) / 2 $in R+
    2 / x > 0
    x + 2 / x > 0
    (x + 2 / x) / 2 > 0

have fn newton_sqrt_two(x R+) R+ = (x + 2 / x) / 2
```

现在可以试几个具体值。用 `litex -session -f accepted-prefix.lit` 一次加载包含上述代码的已通过前缀，再依次向同一个 Session 输入以下三句。初始文件必须通过，才能进入 REPL；不要为每条新候选重新运行文件。失败行概括了 JSON 中的诊断：

```text
litex> newton_sqrt_two(1) = 3 / 2
success
litex> newton_sqrt_two(0) = 1
失败：无法证明 0 $in R+，函数调用的条件不满足。
litex> newton_sqrt_two(3 / 2) = 17 / 12
success
```

第二句停在条件检查：零不属于这个函数的定义域。我们修正输入后，可以沿着此前已经接受的定义和事实继续探索。普通验证失败会丢弃失败语句自身的候选状态，保留已经接受的上下文；进程退出后，则需要重新加载或重放这些成果。

这让反馈直接回到数学问题：输入是否满足条件？下一步能否成立？人和 AI 都可以据此调整下一次尝试。

<a id="workflow-reuse"></a>

### 4.3 把今天的成果，留给下一次探索

算出几个值之后，我们可以证明一个一般性质：如果正数 `x` 满足 `x^2 = 2`，牛顿更新就保持它不变。这一步把具体尝试推进为可以再次引用的数学知识。

<details>
<summary><strong>看一个两文件例子：这里证明，那里使用</strong></summary>

把上一节的函数定义连同它前面的正性证明保存为 `newton.lit`，再在同一文件中加入下面的定理。等式链先得到 `x = 2 / x`，再代入更新公式：

<!-- litex:skip-test -->
```litex
thm fixed_point:
    ? forall x R+:
        x^2 = 2
        =>:
            newton_sqrt_two(x) = x
    x = x * x / x = x^2 / x = 2 / x
    newton_sqrt_two(x) = (x + 2 / x) / 2 = (x + x) / 2 = x
```

在 `litex.config` 中按数学依赖顺序组织两个文件：

```toml
[export]
newton = "./newton.lit"
example = "./example.lit"
```

另一个文件 `example.lit` 取用函数定义，再把已经证明的定理用于 √2：

<!-- litex:skip-test -->
```litex
release obj def newton::newton_sqrt_two
by thm newton::fixed_point(sqrt(2)) => newton::newton_sqrt_two(sqrt(2)) = sqrt(2)
```

验证这个应用时，系统先加载前面的 `newton.lit`。这里的两个片段依赖上述项目上下文。

</details>

<details>
<summary><strong>另一个例子：把康托尔定理用于后续推理</strong></summary>

例如，我们可以自己证明康托尔定理：每个函数 \(f:X\to\mathcal P(X)\) 都会漏掉某个子集，因此不可能是满射。下面先定义“一个子集没有原像”，再用对角集合证明一般结论，最后把它用于一个具体函数。整段代码不使用 `trust`：

```litex
prop has_no_preimage(X set, f fn(x X) power_set(X), D power_set(X)):
    forall a X:
        D != f(a)

thm cantor:
    ? forall X set, f fn(x X) power_set(X):
        exist D power_set(X) st {$has_no_preimage(X, f, D)}

    have D power_set(X) = {x X: not x $in f(x)}

    thm diagonal_nonmembership:
        ? forall a X:
            D = f(a)
            =>:
                not a $in f(a)
        by contra:
            ? not a $in f(a)
            a $in D
            impossible a $in f(a)

    claim:
        ? forall a X:
            D != f(a)
        by contra:
            ? D != f(a)
            not a $in f(a)
            a $in D
            a $in f(a)
            impossible a $in f(a)

    by def $has_no_preimage(X, f, D)
    witness exist E power_set(X) st {$has_no_preimage(X, f, E)} from D

have fn singleton(n N) power_set(N) = {n}
release thm cantor(N, singleton)
obtain missing from exist S power_set(N) st {$has_no_preimage(N, singleton, S)}
missing != singleton(0)
```

这个例子展示了知识怎样在证明中积累并继续使用。定义概念、证明康托尔定理之后，这些成果就成为当前数学背景的一部分。引入具体函数 `singleton` 后，Litex 能继续使用已经证明的一般结论，得到新的对象与事实，供后续推理依赖。

</details>

后一个文件沿用已有定理，继续处理自己的问题。随着这样的成果逐渐积累，定义、构造和定理可以组织为模块，供同一项目或其他项目使用。读者得到的也就不止是一篇完成的证明，还有下一次工作可以依赖的数学词汇与知识。

积累之后，用户可以通过 Litex 的普通 JSON 自行组织数学内容。例如，上面定理的调用会在语句文本中保留名称、参数和选定结论，已接受的事实则记录在 `stores` 和 `infers` 中。这些数据可以用于自己的展示工具；简洁的普通输出并没有记录所有依赖关系。

*当前 CLI 已提供原生数学依赖图；网页目前展示的是 Normal JSON 的关系投影，原生图尚未接入。依赖图用于查看知识关系，独立证明复核仍是第 6 节讨论的另一项工作。*

<a id="workflow-use"></a>
<a id="executable-code"></a>

### 4.4 让数学成果用于计算与交流

保存和复用之外，数学成果还可以继续用于计算，也可以写成供别人阅读的文稿。Litex 正在提供这两种出口，让形式化源码与日常数学工作发生更多联系。

**用于计算。** 在目前支持的实验范围内，已检查的数值定义与 `algo` 片段可以抽取为 Python 或 C。牛顿更新可以写成一个执行入口，并证明它在正数输入上与前面的数学函数一致：

<details>
<summary><strong>展开查看：同一个牛顿更新，转为 Python / C</strong></summary>

下面是完整的独立片段。`# [-extract]` 与 `# [end of -extract]` 选择文件中要抽取的部分；其他语句用于普通验证。执行入口对零输入明确返回 `1`；与正数函数的一致性只在 `x R+` 上证明。

```litex
claim:
    ? forall x R+:
        (x + 2 / x) / 2 $in R+
    2 / x > 0
    x + 2 / x > 0
    (x + 2 / x) / 2 > 0

have fn newton_sqrt_two(x R+) R+ = (x + 2 / x) / 2

# [-extract]
algo newton_sqrt_two_step(x R) R by cases:
    case x = 0: 1
    case x != 0: (x + 2 / x) / 2
# [end of -extract]

claim:
    ? forall x R+:
        newton_sqrt_two_step(x) = newton_sqrt_two(x)
    newton_sqrt_two_step(x) = (x + 2 / x) / 2 = newton_sqrt_two(x)
```

用 `-extractpython -f` 抽取后得到：

```python
def newton_sqrt_two_step(x):
    if x == 0.0:
        return 1.0
    elif x != 0.0:
        return ((x + (2.0 / x)) / 2.0)
    raise AssertionError("unreachable verified Litex cases")
```

同一片段用 `-extractc -f` 可以得到 C：

```c
#include <stdlib.h>

double newton_sqrt_two_step(double x) {
    if (x == 0.0) {
        return 1.0;
    }
    else if (x != 0.0) {
        return ((x + (2.0 / x)) / 2.0);
    }
    abort();
}
```

Python/C 抽取仍限于支持的计算片段。生成代码使用浮点数；Litex 检查的是源码中的数学关系，浮点舍入与溢出还需要另行分析。

</details>

**用于阅读与交流。** 数学源码也可以转换为 LaTeX，让定义、公式和证明步骤进入讲义或文稿。例如，可以对上面的两文件项目使用 `-latex -document -lang zh -f example.lit`，得到可继续编辑的 LaTeX 文稿。

LaTeX 转换负责呈现数学源码，数学验证需要单独运行。

从一次探索到一个可复用的定理，再到计算和交流，这是第四个特点希望连接起来的数学工作流。一次证明的完成，也应当成为下一次数学工作的开始。

<a id="interaction-loop"></a>

## 5. Litex 适合与 AI 交互

_“所谓增强人的智力，就是增强人面对复杂问题的能力……”_

_— Douglas Engelbart，《增强人类智力：概念框架》（1962），引言（节选）_

**Litex 适合 AI agent 逐步交互。** AI 可以把候选写成数学事实，查看验证反馈，修正下一次输入；活动 Session 则保留已接受的知识。每条成功语句都会成为下一次提议可用的上下文。

人负责数学问题、关键构造与最终判断。人或外部工具可以记录失败尝试及其修复过程。逐句验证将这些角色连接成协作工作流。

<a id="session-authoring"></a>

**边写边检查，保留已经正确的知识。** 编写或修复 Litex 代码时，**开启 `-session`，始终保持同一个进程**。普通语句失败不会清除之前已接受的定义和事实。绝不要每加几条新代码，就把整个文件从头重新跑一遍。

**对于有前后依赖的推理，保留 Session 避免了反复重建前缀带来的二次累积。** 设有 $N$ 个依赖步骤，每步验证耗时近似为 $t$，已接受前缀保持不变。在书写循环中，同一个 Session 只验证每个新步骤一次；每次重启则要重新验证不断增长的完整前缀：

$$
T_{\mathrm{Session}} \approx Nt, \qquad
T_{\mathrm{restart}} \approx t\sum_{n=1}^{N} n = t\frac{N(N+1)}{2}.
$$

因此，在这个成本模型下，累计耗时之比为

$$
\frac{T_{\mathrm{restart}}}{T_{\mathrm{Session}}} \approx \frac{N+1}{2}.
$$

**在这个模型中，每次从头验证，时间随依赖链长度二次增长；在同一个 Session 中增量验证，则是线性增长。** 这里计算的是每步提交一次的书写循环，不包含初始上下文加载、单独的阶段/最终文件检查，以及必要的重启重放。实际耗时取决于每步验证成本与运行开销。

先接受一个实数值：

```bash
litex -lang en -session -e 'have a R = 2'
```

随后在同一个进程中逐条输入。失败 JSON 在这里被缩略：

```text
litex> a = 3
{"run_result": "failure", ..., "session_terminated": false, "termination": null}
litex> a + 1 = 3
success
```

失败的 `a = 3` 不会移除 `a = 2`，下一句仍能使用它。对 AI 作者，拒绝反馈给出了具体的停止位置：`why_failed.phase` 为 `"search_proof"`，`why_failed.goal` 为 `"a = 3"`。AI 可以读取这份反馈，利用保留的上下文提出下一句。对照两个独立命令：

```bash
litex -lang en -e 'have a R = 2'
litex -lang en -e 'a + 1 = 3'
```

第一条成功；第二条失败，因为新进程没有 `a` 的声明，必须重新加载已接受的声明。保留 Session，就不必为每次尝试重新构建上下文。保存已接受源码，在连贯的阶段检查点或最终验收时另行运行干净文件检查。如果进程停止或已加载上下文必须改变，则重启并重放已接受源码；[第 4 节的数学工作流](#workflow-exploration)将这条规则用于更长的例子。

**人、AI 与 Litex 的协作循环：**

```text
人类提出数学问题及其解答意图
                         ↓
AI 把问题与解答拆成有序片段
                         ↓
              ┌──── 片段形式化循环 ────┐
              │                         │
              ▼                         │
AI 把当前片段写成 Litex 代码             │
                         ↓              │
Litex 结构化验证结果                    │
   ├─ success                           │
   │     → 记录这段代码                 │
   │     → 记录 Litex 如何运行它        │
   │     → 进入下一片段 ────────────────┘
   └─ 语句被拒绝
         → 基于证据的诊断
         → 在同一个 Session 中修复这条语句，再试
                         ↓
全部成功片段按顺序衔接 → 问题得到解决与形式化
                         ↓
人类专家做基本校验
                         ↓
这些 Litex 代码成为后续其他问题的基石
```

每轮提交一条顶层语句，例如一个定义，或带完整证明的定理。普通失败只丢弃该语句自身的暂存状态。包含多条语句的片段不是一个事务：即使某句失败，其他成功语句也可以提交。如果协作工具保存候选源码及其输出，人和 AI 就能回看修复过程；完整的尝试记录由这些工具维护。在阶段检查点和最终验收时，将已接受语句按顺序保存，再从干净进程验证完整文件。人仍须核对形式陈述是否忠实于原题与数学意图。

<details>
<summary><strong>示例：按流程图走一遍片段形式化循环</strong></summary>

下面的收敛例子展示计划中的片段顺序。两个定义已通过检查；定理证明仍是迁移示例，当前构建尚未验证，因此这个协作过程还没有完成。

<a id="convergence-example"></a>

**1. 人类提出数学问题及其解答意图**

> 先定义数列收敛：对任意正误差 `ε`，存在位置 `N`，使此后每项都足够接近极限。再证明：若 `{s(n)}` 收敛到 `a`，则 `{c * s(n)}` 收敛到 `c * a`。

**2. AI 把问题与解答拆成有序片段**

针对这个问题，AI 可以先拆成例如：

1. 定义“最终足够接近”，这是一个谓词，用`prop`定义
2. 定义“收敛”，这是一个谓词，用`prop`定义
3. 写出并证明 `thm`：数乘保持收敛  

**3. 片段形式化循环：前两个片段成功——先把定义写进上下文**

AI 先提交两个定义；Litex 返回成功。于是留下这段源码，以及 Litex 如何运行它的记录。已接受上下文增长，后面的定理片段可以按定义展开。

```litex
# “最终足够接近”：从 N0 起，每项都落在误差 epsilon 内。
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            |s(n) - a| < epsilon

# “收敛到 a”：任意正误差都存在这样一个 N0。
prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}
```

**4. 同一循环中的失败与修复：证明数乘保持收敛**

若 AI 在没有构造 `forall / exist` 结构时直接 `by def` 要求新数列收敛，局部检查会停下。下面的 JSON 是失败反馈的结构示意，不是这段定理当前运行结果的逐字记录：

```json
{
  "kind": "run",
  "run_result": "failure",
  "detail": "normal",
  "session_terminated": false, "termination": null,
  "statement_results": [
    {
      "statement_result": "rejected",
      "statement": "...",
      "why_failed": {
        "phase": "search_proof",
        "goal": "$converges_to(fn(n N) R {c * s(n)}, c * a)"
      },
      "stores": [],
      "infers": []
    }
  ]
}
```

失败片段不进入已接受上下文。定义只给出要证明的形状；证明仍须为每个 `epsilon` 构造合适的 `N0`。下列片段保留了这一修复思路，但还需要继续迁移和验证：

> **迁移示例：** 当前 `src/` 检查停在 `def_thm` (`thm`)；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
thm converges_to_mul_const:
    ? forall s fn(n N) R, a, c R:
        $converges_to(s, a)
        =>:
            $converges_to(fn(n N) R {c * s(n)}, c * a)
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)}
        |c| + 1 > 0
        epsilon / (|c| + 1) $in R+
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / (|c| + 1), K)}
        witness exist K N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, K)} from N0:
            forall n N:
                n >= N0
                =>:
                    |s(n) - a| < epsilon / (|c| + 1)
                    |c * s(n) - c * a| = |c| * |s(n) - a|
                    |c| * |s(n) - a| <= (|c| + 1) * |s(n) - a| < epsilon
                    |fn(k N) R {c * s(k)}(n) - c * a| < epsilon
            by def $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
    by def $converges_to(fn(n N) R {c * s(n)}, c * a)
```

当前构建在这段 `thm` 的 `def_thm` 阶段停下，因此不能把它或后面的数乘结论写入已接受前缀。

**5. 目标流程：全部片段通过后再衔接**

只有定理片段真正通过验证，定义与定理才会连成连续的 Litex 发展。外部协作工具可以保存失败尝试以解释修复；数学前提仍只来自已接受的源码。

**6. 人类专家做基本校验**

专家还须核对：`prop` 是否忠实于收敛定义，定理是否仍表达数乘保持收敛，估计是否符合原来的数学意图。机器通过不等于免审。

**7. 这些 Litex 代码成为后续问题的基石**

若定理以后通过验证并经人审阅，收敛接口与数乘定理才能作为后续极限或连续性问题的可复用前提。本例目前只展示这条路线及其尚未完成的边界。

</details>

<a id="compatibility"></a>

## 6. 连接 Lean 独立复核，并与 Mathlib 兼容（Experimental）

独立复核必须保留第一大特点中的数学含义与定义域条件。Litex 到 Lean 的编译正在通过可检查的例子逐步扩展。目标是让可读的 Litex 数学发展获得可独立检查的证明，同时保留原来的对象、前提和结论。这条路径由三部分组成：Litex 检查源码，编译器重放记录下来的证据，`lean/Litex.lean`为生成的表达式提供 Lean 中的语义。

### 从任意对象开始

维护中的任意实数例子 (`lean/examples/arbitrary_real_laws/statement.lit`)可以完整读下来：

```litex
have arbitrary_real R
arbitrary_real = arbitrary_real
arbitrary_real + 0 = arbitrary_real
arbitrary_real >= arbitrary_real
```

第一行引入 `R` 的任意成员，不指定某个数值。后面的事实分别表达自反性、加零不变和实数序的自反性。对应的生成 Lean 证明 (`lean/examples/arbitrary_real_laws/statement.lean`)保留具有一般宿主表示的对象，并单独保留成员关系前提 `Litex.In a Litex.R`。知道对象属于实数集合，不会把它的宿主表示替换成 Lean 的 `ℝ`。

这不只是让算术例子更短：翻译必须保留作者真正声明的对象，不能悄悄把任意对象换成方便计算的具体值或表示。

### `Litex.lean` 如何解释对象与事实

`Representation M α` 规定宿主类型 `α` 的哪些值是良定义的，以及它们如何解释为语义宇宙 `M.Value` 中的值。认证对象把值和良定义性证明放在一起。下面是 `lean/Litex.lean`中的实际声明，不是某个问题的生成产物：

```lean
structure Obj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  val : α
  wd : WD (M := M) val
```

不同宿主类型都可以表示 Litex 对象。源码相等比较对象的语义值；成员关系联系元素与集合的语义值。两者都是普通的 Lean 命题，在语义接口中有固定定义：

| 源码含义 | Lean 接口 | 语义内容 |
| --- | --- | --- |
| `a = b` | `Litex.Same a b` | `denote a = denote b`，允许两端使用不同宿主表示 |
| `a $in A` | `Litex.In a A` | `M.mem (denote a) (denote A)` |
| `a < b` | `Litex.Lt a b` | 提供两端的实数语义见证，其值满足 `<` |
| 由公式定义的函数 | `Litex.FormulaFn` | 集合论函数图，带定义域、保护条件和经过检查的返回成员关系 |

因此，`Same` 和 `In` 有确定的数学含义。`Representation` 不会默认认证任意 Lean 类型，`Obj` 也不会让源码中无定义的运算变得可用。算术桥接层将已认证对象的数值语义连接到 Lean/Mathlib 算术，再把经过检查的结果传回原来的源码命题。

### 函数的定义域必须留在证明里

带保护条件的除法例子 (`lean/examples/real_quotient_distributes/statement.lit`)进一步引入函数和命名定理：

```litex
have fn quotient(a, b R: b != 0) R = a / b

quotient(6, 2) = 3

thm quotient_distributes:
    ? forall x, y, z R:
        z != 0
        =>:
            quotient(x + y, z) = quotient(x, z) + quotient(y, z)
    quotient(x + y, z) = (x + y) / z
    quotient(x, z) = x / z
    quotient(y, z) = y / z
    (x + y) / z = x / z + y / z
```

非零保护条件属于函数的定义域。`Litex.lean` 将公式表示为该受限定义域上的函数图，并要求证明函数体返回 `R` 的成员。调用需要函数成员关系、参数成员关系和保护条件；除法对象的构造器还要求分母非零的证明。这保留了 Litex 除法的部分定义，即使 Lean 底层的域除法是全定义运算。

对应的生成证明 (`lean/examples/real_quotient_distributes/statement.lean`)重放函数展开与实际选中的算术等式，包括它们的定义域证据。源码事实和引用保留由原始 FactId 派生的名字。编译器沿已检查的结果生成证明，不让 Lean 重新寻找一个可能已经改变陈述的替代证明。

### 独立复核确立什么

生成定理以 `M : Litex.Semantics` 为参数；集合与函数路线还需要相应的语义接口。这些是必须满足其规律的显式契约，不是无条件断言的全局公理。`Litex.lean` 还提供基于 Mathlib `ZFSet` 的具体 `NumericModel.model`，以及集合、函数接口的实例。这为已经实现的接口提供了具体模型见证，不等于整个 Litex 的所有对象与规则都已有完整模型和编译覆盖。

生成 Lean 源码与通过 Lean 内核检查是两个步骤。对受支持的路线，独立检查验证的是相对于所列语义契约和 Lean 基础的生成命题与证明。更广的覆盖必须通过扩展语义接口和证明重放逐项建立；尚未支持的路线应明确拒绝。

如果最终定理要完全使用普通 Mathlib 概念，还需要 adapter 将这些语义值连接到目标的原生对象与命题。这一步的表示转换和证明需要单独审查。维护中的编译器指南 (`Litex到Lean编译器指南.md`)讲解源码与生成结果，CLI 参考 (`Litex命令行参考.md`)说明调用限制。完整的源码与生成结果在 `lean/examples/` 中维护。

验证检查点（2026-10-10）：本节两个例子均通过严格 Litex 运行、Lean 生成，以及本地固定 Mathlib 环境下的 Lean 4.31.0 检查。这验证这两个例子及其语义接口，不代表整个编译器的覆盖验收。

<a id="ecosystem-role"></a>

## 7. 从验证记录继续构建

_“预测未来最好的方式，就是创造未来。”_

_— Alan Kay，《The Early History of Smalltalk》（1993）_

语言留下了数学源码与验证记录，就可以沿着它们继续构建工具。前面的设计给出了起点，下面列出相应的用途与当前边界：

| 从语言设计延伸的用途 | 相应成果与范围 |
| --- | --- |
| 阅读与审阅数学 | 人可以直接审核的数学对象、条件、中间事实和结论 |
| 组织已检查的知识 | 经过机器检查的事实与验证来源、明确的停止边界，以及被显式标出的可信边界 |
| 连接 Lean 与 Mathlib | 初始的独立文件 Lean 编译与复核，支持有限范围的验证结果（第 6 节，Experimental）；整个系统的覆盖尚未完成，新增 Lean/Mathlib adapter 仍明确分离，由 AI 或人类编写 |
| 证明 → 可执行代码（Experimental） | 把已检查的计算片段转化成可运行的 Python / C（第 4.4 节） |

欢迎带着数学例子、使用反馈或工具想法来交流：litexlang@outlook.com。

<details>
<summary><strong>怎样持续实现这套语言设计</strong></summary>

这条路线有一个规模矛盾：对象、事实、证明与可信边界需要少数设计者持续统筹，才能保持语义一致；实现却涉及大量规则、良定义性路径、证据结果、失败诊断、例子和测试。以 2026 年 10 月 4 日工作树中的已跟踪文件计，当前 `src/` 有 631 个 Rust 文件、约 13.7 万物理行。全仓库的 Rust 文件约 41.9 万行，但其中包含 `scripts/` 下的历史与实验实现，不能都算作当前验证器。这些数字说明工程规模，不证明数学覆盖或正确性。

AI 工具改变的是小团队编写、检查和迭代大量实现工作的成本；它不替人决定数学语义、可信边界或验收标准。集合论式语言、自然可读的证明和局部自动化也各有先例。Litex 要检验的是：把这些选择放进同一个默认工作界面，在新的工程条件下能否形成可读、可检查、可持续扩展的数学工作流。

</details>

<a id="reasoning-direction"></a>

<a id="conclusions"></a>

## 8. 追寻与众不同的艺术

_“数学家像画家或诗人一样，是模式的创造者。”_

_— G. H. Hardy，《一个数学家的辩白》（1940）_

我仍然围绕最初的问题构建 Litex：既然数学本身是一种严格的语言，能不能让它直接成为形式化代码？选择熟悉的对象，规定准确的含义，让作者陈述数学事实，让系统检查依据并解释结果，每一项设计都在回答这个问题。

这个建造过程也在不断改变我对数学、代码与证明的看法。我希望人们能用这样的语言写下自己的数学，读懂检查过程，再从已经建立的知识继续。语言和工具还需要在真实数学工作中不断检验和打磨。

**我希望数学触及并惠及的角落，形式化语言也能触及，Litex 也能。**

<a id="mathematical-values"></a>

### Litex 的数学价值观

Litex 希望维护以下数学价值，与[《莱顿人工智能与数学宣言》](https://leidendeclaration.ai/)的相关主张相呼应：

1. **理解。**[事实导向源码与验证反馈](#fact-oriented-interface)，帮助人看懂每一步。
2. **忠实。**[显式定义、条件与量词](#set-theory)，让人审阅数学意图。
3. **透明。**源码展示证明内容，[验证记录](#execution-model)呈现验证依据。
4. **审阅。**[可重跑验证与模块复用](#workflow-reuse)，帮助同行检查并引用成果。
5. **责任。**[人–AI–Litex 协作](#interaction-loop)中，人选择数学路线并承担责任。
6. **开放。**[开源](https://github.com/litexlang/golitex)与多语种反馈帮助更多人参与；复用仍须注明来源。
7. **诚实。**[Lean 独立复核](#compatibility)（仍在扩展）。

<details>
<summary><strong>作者的话</strong></summary>

我是沈嘉辰（Jiachen Shen），复旦大学数学博士生。Lean 让我看到，数学与编程可以在一门真实语言里相遇；Litex 则探索：形式化源码能否更贴近解数学题时的心流。

今天的 Litex，是在反复试验、重构，甚至推倒重来以后磨出来的。这些过程经常漫长而痛苦，但也让我逐渐看清：哪些写法真正符合数学思考，哪些实现能够长期支撑它们，以及整门语言怎样保持一致。

以我个人的时间和资源，没有 AI 的协助，我无法把这项语言设计推进到今天的代码、文档和例子规模。AI 让一个人有机会持续统筹语言设计，同时承担原本难以独自完成的实现与维护工作。这也是 Litex 的成长与这个时代紧密相连的原因。

Litex 始于个人持续投入，也离不开后来参与者的支持。我希望通过开源的 [golitex](https://github.com/litexlang/golitex) 结识愿意讨论语言设计、数学形式化与 Math for AI 的朋友；批评和不同的实现路线都值得认真对待。

</details>

<a id="special-thanks"></a>

### 特别感谢

Litex 由沈嘉辰与 Litex 团队创建和维护。特别感谢 Wei Lin、Siqi Sun、
Peng Sun、Chenxuan Huang、Yan Lu、Sheng Xu、Keyao Zhu
和 Zhaoxuan Hong 对项目给予的支持与建议。

### 相关链接

1. 如果想直接试用例子，并查看 Litex 生成的输出和知识图谱，可以访问 [litexlang.com](https://litexlang.com)。

2. 如果关注内核实现，可以查看 [golitex 仓库](https://github.com/litexlang/golitex)。

### 原生定理接口与诊断（2026-10-02）

25 个保留的旧定理名称现在在当前验证器中有原生接口约定。定理应用流程在将结论写入周围上下文之前，检查前提与结论的良定义性，并报告实际失败的阶段和前提。含有 `i` 的复数算术由计算处理；索引构造要求索引集非空。这些改动保留了 AST 与 Runtime/ExecEnv 的接口约定；定义端点仍通过显式等式链对齐。支持的参数形式因定理而异；依赖选择公理的积集非空结论会标明其选择公理来源。

<a id="overview-readers"></a>

## 附录：几个语言设计问题

下面从几个具体问题补充前面的设计。每个问题都回到同一件事：数学怎样被写下、检查、理解和继续使用。

| 设计问题 | 例子与讨论 |
| --- | --- |
| 熟悉的符号应该保留什么含义？ | [运算与定义域](#ordinary-mathematics)、[集合论基础](#set-theory) |
| 为什么直接写下一条数学事实？ | [与 Lean 的书写对照](#reader-lean)、[事实导向接口](#fact-oriented-interface) |
| 人怎样看懂并审阅已经检查的证明？ | [源码的阅读与审阅](#reader-mathematicians)、[验证记录](#execution-model) |
| 对象、事实与语句怎样组成一门语言？ | [语言结构与 Python 类比](#reader-programmers)、[系统工程实例](#systems-engineering) |
| 一份已检查的源码还能支持什么？ | [知识复用](#workflow-reuse)、[AI 交互](#interaction-loop)、[Lean 复核](#compatibility) |

<a id="reader-lean"></a>

### 为什么直接写数学事实：与 Lean 的书写对照

为什么还要另一种形式化语言？

我第一次看到 Lean 时，十分震惊：数学居然可以写成代码，证明居然可以交给机器检查！“数学代码化”这个想法本身就让我感到兴奋，也让我开始思考自己希望怎样使用一门形式化语言。

学习过程中，我渐渐有了几个问题。What if，我能直接写下 `1 + 1 = 2`，不用先写 `example`，再接一个 `by ...`？What if，定义了奇数以后，我直接写 `$odd(13)`，语言就能按定义检查它？What if，已经知道“所有人都会死”和“苏格拉底是人”，我就能直接写“苏格拉底会死”，不用再点名引用那条全称前提？

这些问题汇成一个具体的界面选择：作者决定数学上的下一步，语言寻找受支持的局部依据，并说明这一步给上下文留下什么。代价是验证器须承担良定义性、依据匹配、结果记录与失败定位；第 3.1 节已展开这项设计责任。Lean 用户可以据此判断，自己得到的是另一种默认工作流，而不只是几处较短的记号。

```text
Lean:  命题 → 证明目标 → tactic 精化 → 证明项 → 内核检查
Litex: 对象与事实 → 内核检查并检索依据 → 已验证事实扩展上下文
```

Lean 把对象、命题和证明纳入依赖类型论的 term/type 体系；Litex 在源码中区分数学对象、事实以及定义和证明步骤。下面的 subtype 对照展示：当函数调用的条件已经成立时，两种语言怎样写出这个调用。这里比较的是表达方式和阅读成本。

Lean 仍是 Litex 的重要参照与复核目标。Lean 的证明经精化成为由内核检查的证明项；面向可执行程序的编译器 IR 是另一条路径。当前独立文件编译器已将受支持的结果回放到 Lean；更广的覆盖仍需逐条验证。性能或学习成本上的优势也不能只凭界面推断，须在可比任务上测量。

<details>
<summary><strong>Lean–Litex 对照示例</strong></summary>

下面直接放三组代表性 Lean–Litex 对照代码。为保持表格简洁，Lean 示例省略了 `import` 行。它们比较的是默认接口，不是证明长短，也不声称两种语言的能力边界完全相同：

<table>
<thead>
<tr><th>Litex 示例</th><th>Lean 示例</th></tr>
</thead>
<tbody>
<tr>
<td><strong>直接事实：已知 x = 2</strong><pre><code>forall x R:
    x = 2
    =&gt;:
        x + 1 = 3
        x^2 = 4</code></pre></td>
<td><strong>同一事实</strong><pre><code>example (x : ℝ) (h : x = 2) :
    x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩</code></pre></td>
</tr>
<tr>
<td><strong>带条件的函数定义域</strong><pre><code>forall x {y R: y &gt; 0}:
    x &gt; 0

have fn positive_successor(x R: x &gt; 0) R = x + 1

positive_successor(1) = 2</code></pre></td>
<td><strong>用 subtype 携带条件</strong><pre><code>def positiveSuccessor
    (x : {y : ℝ // y &gt; 0}) : ℝ := x.val + 1

example : positiveSuccessor ⟨1, by norm_num⟩ = 2 := by
  norm_num [positiveSuccessor]</code></pre></td>
</tr>
<tr>
<td><strong>交集保持子集关系</strong><pre><code>forall s, t, u set:
    s $subset t
    =&gt;:
        intersect(s, u) $subset intersect(t, u)</code></pre></td>
<td><strong>展开集合定义并逐点证明</strong><pre><code>example {alpha : Type*} (s t u : Set alpha) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩</code></pre></td>
</tr>
</tbody>
</table>

</details>

<details>
<summary><strong>展开两个门槛例子</strong></summary>

下面两个例子讨论从“我明白”到“我能形式化”还需要跨过的门槛：

1. **工具使用门槛**：用户已经理解一个数学事实，却未必知道怎样把它写进形式系统。
2. **表达方式门槛**：形式系统中的数学写法，可能与我们熟悉的日常数学表达不同。

先看工具门槛。很多时候，数学本身已经够简单——例如小朋友也会写的 `1 + 2 = 3`，或一条多项式恒等式——卡在形式系统里的，往往不是“懂不懂数学”，而是记不记得该调用哪个 tactic、哪条引理。

Litex：

```litex
1 + 2 = 3

forall a, b R:
    (a + b)^2 = a^2 + 2 * a * b + b^2
```

Lean：

```lean
import Mathlib

example : (1 : ℝ) + 2 = 3 := by norm_num

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
```

Lean 版本很有用，却要求用户先知道：数值等式用 `norm_num`，多项式用 `ring`；更复杂时还要记住定理库里的事实名，并在源码里显式调用。这些名字和调用步骤不是数学事实本身，却常常占掉大量时间与精力。Litex 追问：用户理解事实后，能否直接写下它，由系统完成检查所需的工具工作——而不必先学会记忆、检索并点名调用那些依据？

再看表达门槛。我们的数学问题是，函数 `f` 只接受正实数，且已知 `x > 0`；我们想说明 `f(x)` 等于自身。Lean 的一种常见编码是：

```lean
example
    (f : {x : ℝ // x > 0} → ℝ)
    (x : ℝ) (hx : x > 0) :
    f ⟨x, hx⟩ = f ⟨x, hx⟩ := rfl
```

对应的 Litex 是：

```litex
forall f fn(t R: t > 0) R, x R:
    x > 0
    =>:
        f(x) = f(x)
```

Lean 用子类型（subtype）把值与其为正的证明绑定，因此调用时组合 `x` 与 `hx` 为 `⟨x, hx⟩`。设计精确通用，但读者须越过这层表示才能看到 `f(x)`。

Litex 仍检查 `x > 0`，但让它作为普通事实留在上下文中，源码仍写 `f(x)`。省去的是手工传递证据；对 `f(x)` 的良定义性检查由验证器替您完成。

> **用户写下事实，系统检查可用依据。** 对受支持的步骤，`1 + 2 = 3` 无须手写 `by norm_num`；条件已知时，函数调用也无须在源码里反复传递证明。这能减少一部分操作，但总体门槛仍需由真实使用检验。

目前 AI for Math 行业遇到的问题是：AI 可能生成通过 Lean 内核的代码，但实际命题少了条件、改变了量词或弱化了结论。Lean 内核没有出错；它正确检查了代码中的命题。错在形式陈述没有对齐数学意图。

理想状态下，Litex 用户关注对象、条件、事实和结论，Litex 提供局部可追踪的反馈。*理解领域却并非证明助手专家的人，也能参与形式化，并知道系统检查到了哪里。*

> **这是设计方向，不是对当前语言、标准库或编译器已经完备的声明。**

</details>

<a id="summary-bottom-up-and-top-down"></a>

<details>
<summary><strong>个人思考：目标引导与事实积累</strong></summary>

从前提出发积累中间事实，与从目标出发分解证明义务，都是数学工作中有用的方向。Litex 的默认源码偏向前者；Lean tactic 的常见交互偏向后者。AI 究竟在哪一种表示下更容易提出正确步骤、利用失败反馈和复用中间结论，是可以比较的研究问题，不能仅从训练方式推断。

理想的协作流程可以同时利用两种方向：先用目标选择有价值的路线，再逐句积累可检查的事实。Litex 初始的独立文件编译器已提供有限范围的 Lean 交接；要在整个系统上连接这两种工作方式，仍须扩展结果覆盖并验证语义。

</details>

<a id="reader-mathematicians"></a>

### 人怎样阅读和审阅已检查的证明

**数学家需要一种既能由机器检查，又能由自己读懂、修改和引用的证明载体。** 人与 AI 共同探索数学，是 Litex 设计所面向的工作方式。AI 可以协助提出构造、补全证明和修改表达；数学家仍要判断问题是否值得研究、定义是否恰当，以及证明是否带来了理解。

这种协作首先带来检查能力的压力。复杂论文的审阅可能经历漫长的人工核查；如果候选证明持续大量生成，仅靠逐篇人工检查，很难让检查能力随产量一起增长。形式化语言提供了一条路径：把定义、前提、结论和推理步骤明确写下，让机器承担可形式化的逻辑检查。对于已经完成形式化、且处于验证器支持范围内的证明，其他人可以重新运行检查，减少重复人工核查的负担。论文的数学意义、原创性、解释质量与学术归属，仍需要共同体判断。

形式化也改变了证明的引用方式。读者可以看到某个结果的准确陈述、适用条件和依赖，并在后续证明中使用它，由系统检查引用是否满足前提。这样的引用能把证明逐步积累成可继续构造的共同知识；它仍须保留作者、来源和版本信息。蓝图的[工作流与复用](#workflow-reuse)部分讨论了 Litex 如何为这条路径留下记录。

但机器能够检查，还不足以让数学家掌握这份知识。Lean 等成熟系统提供了严格的验证与丰富的数学库，也要求使用者学习新的表达方式、证明接口和库组织。AI 可以帮助生成代码，却不能保证作者理解代码中的命题与证明。数学家可能理解自己原本的论证，却难以判断生成的形式化版本是否漏掉条件、改变了量词，或证明了一个较弱的结论。验证器检查的是代码实际表达的命题；数学意图与形式化陈述是否一致，仍需要作者审阅。

**AI 降低了生成形式化代码的成本，语言仍须降低人理解和掌握这些代码的成本。** 如果承载自己思想的证明文本无法由自己审阅和修改，数学家就难以对其表达负责，也难以从他人的证明中学习和继续探索。[陶哲轩等 25 位菲尔兹奖得主在 2026 年 9 月的声明](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/)强调，快速产出答案不能取代概念理解、思想传播与数学共同体的消化过程。

**数学理解的一个重要方面，就是看见联系（seeing connections）。** 维特根斯坦在[《哲学研究》第 122 节](https://www.wittgensteinproject.org/w/index.php?title=Philosophische_Untersuchungen)把理解与“看见联系”联系起来。他谈论的是清晰呈现语言用法如何带来理解；用来思考数学，这提示我们追问：一个结论怎样从定义和假设中生长出来，中间步骤为何相连，同一结构又能在哪些问题中复用？

读 Litex 证明时，可以把源码与 [JSON 知识记录](#execution-model)对照起来：这一句用了什么前提，引用了哪条事实，又为下一步留下了什么？Detailed 输出提供更细的前提与引用记录。[前面的例子](#overview-readers)展示了作者怎样写下数学步骤，再查看它们的验证依据。

我希望数学家能读懂、修改 AI 写下的证明，发现它与自己原意的偏差，并从中找出可复用的想法。这样的写法究竟能节省多少学习和审阅时间，需要在真实任务中测量。

<a id="reader-programmers"></a>

### 对象、事实与语句怎样组成一门语言

程序员可以把 Litex 看成一种分别表达数学对象、事实和证明步骤的语言。Lean tactic 证明常通过指令改变目标状态；Litex 的日常写法是直接陈述事实，由验证器检查表达式的良定义性，并寻找局部依据。

“像 Python”说的是：语言处理许多日常操作，让作者专注于想表达的数学。在 Litex 中，这包括为普通事实选择局部验证方法、检查前提并复用结果。同一对象也可以被证明属于多个集合，函数调用所需的成员与条件事实由验证器检查。这里的类比侧重使用体验；Litex 的成员事实与良定义性检查仍有自己的数学含义。

```text
Lean 表面:  terms / types   （对象、命题和证明由项与类型表达）
Litex 表面: 对象 · 事实 · 语句

Lean（作为语言）: 函数式 / 声明式
Lean tactic 证明:  常读作命令式 how
Litex 源码:        声明式 what；验证器寻找 how

Lean（写数学时）:  严格类型手感  ≈ static
Litex:             多集合归属    ≈ dynamic（偏 Python）
```

事实表与规则表把一部分依据检索工作从作者转移给语言；[第 2 节](#fact-oriented)说明这条默认路径的搜索边界，[验证实现的分工](#automation-implementation)解释相应的工程成本。作者能少写许多操作，是因为每条受支持的路径都在实现中处理了前提、结果与失败反馈。

还有第二条程序员常关心的实验性编译路线：计算片段在 Litex 里检查过之后，可以尝试抽出可运行的 Python 或 C（第 4.4 节）——同样标明实验性，且范围很窄，不是整门语言的后端。

<a id="reader-other-domains"></a>

### 这套设计可以延伸到哪里

我希望，在数学被使用的地方，人们也有机会使用形式化工具。把这套设计用于新的领域，需要先明确对象、关系、假设和规则，再用具体例子检验语言能否忠实表达并检查它们。这仍是从数学语言设计出发的探索。

<a id="systems-engineering"></a>

## 附录：从系统工程的角度看 Litex

先看一个定义与一次验证：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

第一句定义非零实数上的倒数函数，第二句验证它在 `2` 处的值。这两行把三类设计连接在一起：

| 系统中的角色 | 例子中的具体内容 | 怎样参与这两步 |
| --- | --- | --- |
| 对象（Obj） | `reciprocal`、`x`、`1 / x`、`reciprocal(2)` | 表达函数、参数、函数体和调用；各自的使用条件需要检查。 |
| 事实（Fact） | `x $in R`、`x != 0`、`reciprocal(2) = 1 / 2` | 表达参数条件与待验证的等式。参数条件在相应的局部作用域中使用；通过验证的等式供后续步骤引用。 |
| 语句（Stmt） | `have fn ...` 与下一行的事实语句 | 建立已检查的函数定义，再请求验证一个事实；成功后记录结果并扩展当前上下文。 |

定义函数时，系统要在参数条件下检查 `1 / x` 是否有意义、是否满足声明的值域，并把签名与函数体关联起来。验证第二句时，要检查 `2` 属于实数且满足非零条件，再利用函数定义建立等式。当前 Normal 输出将第二句的依据标为 `object_definition`，并把 `reciprocal(2) = 1 / 2` 存入可用事实。

如果把第二句改成 `reciprocal(0) = 0`，检查会停在函数调用的良定义性：参数条件要求 `0 != 0`，这一条件不能成立。失败语句不把这个等式加入已接受上下文。函数对象、条件事实、定义展开、等式验证、知识保存与失败反馈，必须在同一套流程中衔接。

随着表达式和证明结构继续组合，这些衔接会涉及更多分支。[事实导向接口](#fact-oriented-interface)说明如何按目标形状寻找局部依据，以及检查规则前提时怎样限制查找权限。这里的系统工程问题，是让每条受支持的路径都交代条件、依据和上下文变化，并使这些路径能够配合使用。

Litex 的核心工作，是寻找一套能够支撑日常数学推理的表达与验证机制。经过持续的试验、重构和真实证明的检验，我逐渐磨出了一套职责一致、能够相互组合的对象（Obj）、事实（Fact）与语句（Stmt）系统，并为它们之间常见的数学关系建立了对应的机械验证流程。

这项工作的难点，集中在大量细小步骤之间的衔接。一个普通数学事实，可能同时涉及对象范围、函数条件、定义展开、等式替换、规则前提和作用域。每个环节本身往往并不艰深，但它们必须在不同组合中保持一致。必要的支持缺失时，作者就需要反复补写本可机械完成的步骤；验证流程组织不当时，系统又可能找不到已有依据，或付出不必要的搜索成本。

Litex 的迭代，就是不断从真实数学中发现这些断点，修正表达模型、补齐必要的关系，并调整验证流程，让更多常见步骤能够在明确的前提和受控的查找范围内自动完成。作者仍然选择数学构造和关键证明路线，语言承担其中可机械检查的衔接工作。用户最后看到的几行源码，背后是大量分支经过反复协调后形成的共同机制。

AI 使我能够以个人的时间和资源，持续推进这种密集的设计循环：提出一种组织方式，实现它，用真实证明检验，再根据失败重构。我的工作是在这些循环中逐渐确定哪些分类、关系和验证流程能够长期配合；AI 则让我有能力把大量细节实现、检查并反复修改。以我个人的时间和资源，没有 AI 的协助，我很难在约两年的时间里完成同等密度的探索与实现。

<a id="overview-gallery"></a>

## 附录：源码速览（gallery）

下面几段不是教程，只展示「直接写要证的东西」在 Litex 里长什么样；设计与边界见前文各节。

最简单的等式：

```litex
1 + 1 = 2
```

多项式恒等式：

```litex
forall a, b R:
    (a + b)^2 = a^2 + 2 * a * b + b^2
```

集合事实：

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

非负数相加仍非负：

```litex
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y
```

定义域条件已知时的良定义调用：

```litex
forall f fn(t R: t > 0) R, x R:
    x > 0
    =>:
        f(x) = f(x)
```

谓词——先定义，再当作原子事实使用：

```litex
prop is_positive(x R):
    x > 0

forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)
```

已知全称事实，用来推出具体的原子事实：

```litex
prop is_positive(n R):
    exist a R+ st {n > a}

claim:
    ? forall x R:
        x > 10
        =>:
            $is_positive(x)
    witness exist a R+ st {x > a} from 10

have a R:
    a > 10

$is_positive(a)
```

存在量词——先见证，再从 `exist` 事实取出对象：

```litex
witness exist x R st {x = 0} from 0

obtain zero from exist x R st {x = 0}
zero = 0
```

定理——命名可复用结论，再按需引用（整除传递性）：

```litex
prop divides_by(d, n Z):
    exist k Z st {n = d * k}

thm divides_transitive:
    ? forall a, b, c Z:
        $divides_by(a, b)
        $divides_by(b, c)
        =>:
            $divides_by(a, c)
    obtain k from $divides_by(a, b)
    obtain m from $divides_by(b, c)
    c = b * m = (a * k) * m = a * (k * m)
    witness $divides_by(a, c) from k * m:
        c = a * (k * m)

witness $divides_by(2, 6) from 3
witness $divides_by(6, 30) from 5

by thm divides_transitive(2, 6, 30) => $divides_by(2, 30)
```

具名函数：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

局部证明块 `claim`——写出沿途应当成立的等式，不必点名改写方向：

```litex
claim:
    ? forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    a * (b * g) = (a * b) * g = (c * d) * g = (c * d) * f = c * (d * f)
```

反证法——否定「每个实数都满足 `x^2 >= x`」：

```litex
by contra:
    ? not forall x R:
        x^2 >= x
    impossible 0.5^2 >= 0.5
```

分类讨论——穷尽分支，再在每个分支里关闭目标：

```litex
have fn k(x R) R by cases:
    case x = 2: 3
    case x != 2: 4

have x R

by cases:
    ? k(x) > 2
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
```

归纳法——前 `n` 个正奇数之和等于 `n^2`：

```litex
have fn kth_odd(k Z) Z = 2 * k - 1

thm sum_first_odds:
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ? sum(1, n, kth_odd) = n^2

        ? from n = 1:
            kth_odd(1) = 2 * 1 - 1 = 1
            sum(1, 1, kth_odd) = kth_odd(1) = 1 = 1^2

        ? induc:
            kth_odd(n + 1) = 2 * (n + 1) - 1
            sum(1, n + 1, kth_odd) = sum(1, n, kth_odd) + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2
```

结构体——群：载体上的运算、单位元、逆元，以及单位元唯一性：

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

模板——按参数族实例化定义，再用 `\name<args>` 取出：

```litex
struct Triple<X set>:
    first X
    second X
    third X

template<X set>:
    have fn triple(a, b, c X) &Triple<X> = (a, b, c)

\triple<R>(1, 2, 3) = (1, 2, 3)

have p &Triple<R> = \triple<R>(1, 2, 3)
p.first = 1
```

一道简单应用题——当前解析器使用 ASCII 变量名，注释可以写中文：

```litex
# 妈妈年龄是小明年龄的 3 倍再加 4；小明 15 岁。妈妈几岁？
have xiaoming_age R = 15
let mom_age = 3 * xiaoming_age + 4
mom_age = 3 * 15 + 4 = 49
```

你写出数学步骤；Litex 检查每一步的衔接，并把通过的事实留在上下文里。

精确十进制在构造时规范化，`2.400` 与 `2.4` 在比较和持久化时具有一致的数值。
虚数单位有专用非零 builtin；复数除法保留分母证据。有限求和与求积由求值器和
等式验证器共享计算：检查函数应用、按绑定身份代入、递归精确求值、再累加或累乘。
一次求值中的嵌套聚合共同使用 1024 项预算，整数端点运算检查溢出。符号规则单独
保留定义域、逐点相等或区间分拆前提。Detailed 输出展示每项计算；`eval` 展示精确值，
核验算法步骤的定义方程后，把“原表达式等于结果”存入当前作用域。
这些验证器能力不代表已有 Lean 导出支持。

<a id="claims-deliverables-evidence"></a>

## 项目主张、实际交付与检查证据

下面汇总本文介绍的现有功能。每一项都附有源码例子、检查记录或支持范围的说明。

| 当前主张 | 已有实现 | 例子与检查记录 | 适用范围 |
| --- | --- | --- | --- |
| 熟悉的运算保留文档说明的含义与定义域。 | 算术语义与良定义性检查。 | [减法与带条件的除法](#ordinary-mathematics)，以及[倒数函数的系统工程例子](#systems-engineering)。 | 已展示的运算接口；是否忠实对应预期数学陈述仍须单独审阅。 |
| 作者可以直接陈述数学事实，由系统检查受支持的衔接。 | 数学对象、事实与定义，良定义检查和局部验证流程。 | [事实导向的源码与验证路线](#fact-oriented-interface)、[源码速览](#overview-gallery)和[系统工程实例](#systems-engineering)。 | 已实现的对象与证明接口，以及验证器明确采用的基础和假设。 |
| 已接受的知识可以支持后续数学工作。 | 保留的事实、可复用的定义与定理、引用和模块机制。 | [每条语句留下的知识记录](#execution-model)和[已有成果的复用](#workflow-reuse)。 | 原有前提、作用域与导入规则下的复用；具体数学开发有各自的检查状态。 |
| 人和 agent 可以修复当前步骤，同时保留此前接受的上下文。 | 持续 Session、结构化失败反馈和 JSON 结果。 | [Session 交互实例](#interaction-loop)和[验证记录](#execution-model)。 | 实例展示的交互与上下文保留行为；写作耗时和证明质量的变化需另行测量。 |
| 一个明确的数学子集已经能编译到 Lean，并连接普通 Mathlib 数学。 | typed result 驱动的编译器、Lean 语义核心、源码／生成文件对与表示桥接；完整原生案例还包含手写 Adapter。 | [Lean 独立复核](#compatibility)、其中注明日期的验收记录及链接的编译器指南。 | 已审查的源码到 Lean 路线和通过检查的例子；原生使用还依赖对应接口的模型与 Adapter。 |
| 数学源码和结果可以供其他工具使用。 | JSON 输出、LaTeX 导出与实验性的 Python/C 抽取。 | [结构化知识记录](#execution-model)与[计算与交流](#workflow-use)。 | 各工具支持的输入输出契约；LaTeX 导出呈现解析后的源码而不执行验证，可执行代码抽取处理受支持的计算片段。 |

## 写给读者

欢迎大家对 Litex 做压力测试——难证、边界情况和真实数学工作，最能看出哪里站得住、哪里还需要打磨。项目人手和资源都很有限，不少地方仍不成熟。希望读者多包涵这些还不完善之处，用建设性的反馈互相支持，一起把工作往前推，而不是把每个不成熟的细节都当作互相指摘的把柄。
