# Litex：让数学自我验证的形式化语言

文档由沈嘉辰创建和维护。

最后更新：2026 年 10 月 8 日。

官网页面: https://litexlang.com/doc/Litex中文蓝图

英文版: https://litexlang.com/doc/Litex_Blueprint

## 目录

- [0. Litex 蓝图总览](#overview)
  - [0.1 五条主线：Litex是怎么工作的](#overview-spine)
- [1. 写下事实，看到成立的依据](#fact-oriented)
  - [1.1 事实导向：把“什么成立”写进源码](#fact-oriented-interface)
  - [1.2 每句话都留下什么：可检查知识记录](#execution-model)
- [2. 从熟悉的数学世界开始：Litex 的集合论基础](#set-theory)
  - [2.1 设计难处：把具体的数学写法做成工作语言](#design-difficulty)
- [3. 让已建立的知识继续生长：自下而上的证明](#bottom-up)
- [4. 人、AI 与 Litex 共同推进证明](#interaction-loop)
- [5. 连接 Lean 独立复核，并与 Mathlib 兼容（Experimental）](#compatibility)
- [6. 从语言到生态：Litex 想扮演什么角色](#ecosystem-role)
  - [6.1 把证明编译成可执行代码（Python / C）（Experimental）](#executable-code)
- [7. 追寻与众不同的艺术](#conclusions)
  - [特别感谢](#special-thanks)
- [附录：编程、数学与Litex形式化](#overview-readers)
  - [个人思考：Litex补齐了AI推理的范式缺口？](#summary-bottom-up-and-top-down)
- [附录：源码速览（gallery）](#overview-gallery)

<a id="overview"></a>

## 0. Litex 蓝图总览

_“语言是人类理性的工具，而不只是表达思想的媒介。”_

_— George Boole，《思维的规律》（1854），第 II 章（节选）_

*Litex 始于 2024 年，想回答一个问题：形式化语言能否成为每个愿意学习的人都能日常使用的数学语言，既贴近熟悉的数学表达，又接受严格检查？它希望成为形式化语言里的 Python，让更多人逐步成为形式化专家。*

**促进理解，是 Litex 的核心追求。** 数学帮助我们理解世界；AI 时代，尤其需要珍惜对数学本身的理解。这一追求体现在两个相连的方面。

**一方面，让数学以熟悉的面貌出现。** Litex 尽量沿用日常数学中的对象和书写习惯：用集合、元素、函数和关系组织数学，直接陈述条件、事实与结论。目的是让读者沿用已有的数学直觉，降低学习和理解形式化表达的门槛与成本。

**另一方面，让数学的结构更清楚。** 对照源码与验证记录，读者可以追问定义、条件和结论怎样相互依赖，一项知识如何建立，又怎样成为后续推理的依据。Litex 希望由此帮助人们在形式化的过程中[加深理解](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/)、发现联系并获得灵感。

写出可检查的证明，除了理解数学，还常要知道该引用哪条定理、怎样调用证明工具。Litex 把许多常见步骤的验证方法交给语言选择和组合：作者写下定义、构造和中间结论，语言从当前知识、内置规则和定义中寻找局部依据，并检查适用条件。

作者可以先写出本步应当成立的事实，再看语言找到的依据或指出的停止位置。通过验证的事实会留下来，供后面的推理使用。Litex 用集合、元素、函数和关系组织这些内容，让人和 AI 能围绕明确的反馈协作。数学路线由作者决定；语言在支持范围内处理方法选择、前提检查和验证步骤的组合。[第 1.1 节](#fact-oriented-interface)用例子说明这种分工，以及它需要怎样的验证实现。

这条路径的下一站是 Lean。Litex 到 Lean 的编译器尚未接入当前构建，预计在 2026 年底完成。它的目标是把支持范围内的 Litex 证明交给 Lean 独立复核，让读者从熟悉的数学表达走进现有的形式化生态。

<a id="overview-spine"></a>

### 0.1 五条主线：Litex是怎么工作的

**这五条主线说明 Litex 如何逐步建立可检查的数学知识，并将其用于 Math for AI。**

**1. 我写下要证明什么，语言告诉我为什么成立。**

我仍然需要思考证明、选择构造和中间结论。但对于可以从当前知识中找到的局部依据，我希望语言能主动完成检查，并向我解释它找到了什么。

例如，我可以直接写下一条计算事实：

```litex
1 + 1 = 2
```

下面并列展示当前 CLI 输出中对应的英文和中文语句记录；Litex 当前支持 10 种输出语言。`proof_method`（中文为 `证明方法`）说明依据，`stores`（中文为 `存储`）记录后面可以继续使用的事实：

<table>
<thead>
<tr><th>英文（<code>-lang en</code>）</th><th>中文（<code>-lang zh</code>）</th></tr>
</thead>
<tbody>
<tr>
<td><pre><code class="language-json">{
  "success": true,
  "statement": "1 + 1 = 2",
  "proof_method": {
    "type": "by_closed_calculation",
    "rule_name": "Closed calculation",
    "message": "Exact evaluation of closed expressions without proof search"
  },
  "stores": ["1 + 1 = 2"],
  "infers": []
}</code></pre></td>
<td><pre><code class="language-json">{
  "成功": true,
  "语句": "1 + 1 = 2",
  "证明方法": {
    "类型": "封闭计算",
    "规则名": "封闭计算",
    "说明": "精确计算封闭表达式，不递归搜索证明"
  },
  "存储": ["1 + 1 = 2"],
  "推断": []
}</code></pre></td>
</tr>
</tbody>
</table>

我也可以先定义奇数，再写下一个具体判断：

```litex
prop is_odd(x Z):
    x % 2 = 1

$is_odd(3)
```

这句 `$is_odd(3)` 对应的 JSON 记录说明，语言通过展开定义完成检查，并留下定义中的具体事实：

```json
{
  "success": true,
  "statement": "$is_odd(3)",
  "proof_method": {
    "type": "by_definition",
    "rule_name": "By definition",
    "message": "Verified by unfolding a definition"
  },
  "stores": ["$is_odd(3)"],
  "infers": ["3 $in Z", "3 % 2 = 1"]
}
```

这些记录让人和 AI 都能看到：这一句检查是否成功，语言找到了哪一种依据，以及这一步留下了什么。

**多语种验证反馈。** CLI 可以用多种语言呈现这些 JSON 验证反馈。同一段源码执行 `litex -lang zh -e '1 + 1 = 2'`，会得到中文字段名与说明；选用 `-lang fr` 则得到法文反馈。感谢 AI 工具在翻译上的协助，使多语种验证说明成为可能；选择输出语言不会改变 Litex 源码或验证结果。当前支持的输出语言代码是 `en`、`zh`、`zh-hant`、`fr`、`ru`、`es`、`ar`、`ja`、`ko` 和 `vi`。

**2. 我可以从已经熟悉的数学世界开始。**

Litex 以 ZFC 为基础，用集合、元素、函数与关系组织数学。我希望读者学习形式化时，能尽可能继续使用原有的数学直觉与表达习惯。

例如，把实数、集合、函数和关系放在同一个小例子里：

```litex
have a R = 2

have S set = {x R: x > 0}

have fn f(x R) R = x^2

prop is_less(x, y R):
    x < y

$is_less(2, 4)
```

`have a R = 2` 同时引入了 `a $in R` 和 `a = 2`。`S` 是正实数集合，`f` 是实数上的平方函数，`is_less` 表达两个实数之间的小于关系；最后一句验证了具体关系 `2 < 4`。这些对象沿用日常数学中的组织方式。

**3. 我们已经建立的知识，语言能够记住并继续使用。**

证明每前进一步，都应留下后面可以依赖的东西。对象、定义与已验证事实共同构成当前的数学背景，让新的推理在这个背景上继续生长。

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

**4. AI 可以和人一起，在明确反馈中推进证明。**

AI 可以协助尝试不同思路、补充步骤和修正错误；人关注问题本身与数学意义；Litex 提供验证反馈。三者共同工作的过程，应当能够积累可检查的成果。

```mermaid
flowchart LR
    Human["人：问题与数学判断"] --> AI["AI：提出并修正证明"]
    AI --> Litex["Litex：验证与反馈"]
    Litex --> AI
    Litex --> Knowledge["已验证的知识"]
    Knowledge --> Human
    Knowledge --> AI
```

**5. 写出的证明，最终还能交给 Lean 再检查一次。**

我希望这些更贴近日常数学的表达，能够编译为 Lean 证明对象，接受独立复核并连接现有生态。当前构建尚未接入这个编译入口，它仍是 Litex 要继续实现的目标。

例如，一条 Litex 计算事实：

```litex
1 + 1 = 2
```

沿用仓库早期编译实验的表示方式，对应的 Lean 证明可以写为：

```lean
import Litex

theorem one_add_one : Litex.Same ((1 : ℂ) + (1 : ℂ)) (2 : ℂ) := by
  exact Litex.Same.ofEq (by norm_num)
```

`Litex.Same` 是编译层中的相等关系。上面的最小 Lean 片段已由 Lean 检查；它展示目标证明的形式，当前 Litex 构建仍未提供生成它的编译入口。

无论你是数学家、程序员，还是 Lean 用户，都可以从 Litex 中发现新的知识与视角；感兴趣的话，可以继续阅读文末的[编程、数学与Litex形式化](#overview-readers)。

后文依次展开这五条主线，最后讨论语言生态；读者比较与更多源码例子放在附录。

<a id="fact-oriented"></a>

## 1. 写下事实，看到成立的依据

_“可读性很重要。”_

_— Tim Peters，《Python 之禅》（PEP 20）_

<a id="fact-oriented-interface"></a>

### 1.1 事实导向：把“什么成立”写进源码

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
`cos(x)!=0`。这两条固定规律没有恢复一般三角展开器，
[持久例子](../examples/proof_nodes/equal/by_builtin_rule/tan_cot_product.lit)
保存了迁移前后的行为。

负或非正公共因子的反序规则分两步：验证因子符号，再验证反向的参数序。
四种比较、四种乘法位置各有独立证据，共16个叶子。固定的反写或更强
前提候选沿用调用权限，并保留实际验证结果；没有新增全局规范化或搜索
阶段，既有正/非负路线仍优先。[弱序例子](../examples/proof_nodes/atomic/by_builtin_rule/nonpositive_common_factor_weak_order.lit)
保留了严格序不能使用零因子的边界。

第一象限规则读取实际的严格条件 `0<x<pi/2`，保留两个来源引用。两条
非零规则供正切、余切既有的良定义检查消费；四个独立的 Less/Greater
叶子在良定义之后证明正性。没有新增搜索阶段或持久状态，
[持久例子](../examples/proof_nodes/atomic/by_builtin_rule/trig_first_quadrant.lit)
检查了这些生产和消费路线。

固定区间检查接受负半圆周端点的四种字面写法及比较的两个方向，保留实际
验证的条件。已存数字等式的替换沿原标量表达式遍历：先匹配整个已知值，
再处理子项；处理子项后形成的父表达式也可匹配已知值。选中的等式都有
真实引用，剩余目标沿用既有权限，表项顺序不会决定原子项是否仍可匹配。
[数字替换例子](../examples/proof_nodes/atomic/by_builtin_rewrite/closed_numeric_subterm_priority.lit)
记录了这个行为，搜索阶段与持久状态保持原合同。

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

这里的“验证内核”指项目中的验证与执行实现，包含依据搜索、内置数学规则、良定义检查、事实存储和反馈。[Lean 的语言参考](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)将精化与 tactic 执行和检查核心证明项的可信内核分开；比较代码规模时需要区分这些职责。当前验证依赖 Litex 验证器及其内置规则、推理规则的正确性；[第 5 节](#compatibility)说明独立 Lean 复核的目标与现状。

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
| 内置改写 / 内置谓词定义路径 | 5 / 11 | 分别统计的结果分支，不并入上面的规则数 |
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

**用户提供的全称事实。** 已证明的 `forall` 事实会进入上下文；遇到同形目标时，Litex 匹配参数并检查实例化后的前提。 整条来源复用也会对齐嵌套 `forall` 前提和 `exist!` witness 中的绑定变量；完整载体、条件和自由对象身份必须保持，WD 仍按调用者原权限检查。这是结构比较，不增加搜索路线。[嵌套来源例子](../examples/proof_nodes/forall/known_source_nested_unique.lit)保存了实际存储事实的引用。

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

<a id="execution-model"></a>

### 1.2 每句话都留下什么：可检查知识记录

每条通过验证的语句都为后面的证明增加可用的知识。执行结果记录本步的顶层依据、存入的事实和适用范围内的推断；失败时则指出停止位置。读者把源码和结果放在一起，就能看见这一步如何成立、又留下了什么。更完整的验证证据保留在内部结果树中，供详细工具和未来的 Lean 复核使用。

先看一个最小的连续片段：

```litex
let a = 1
a + 1 = 2
```

第一句是定义（`define`）：它引入对象，并把定义事实 `a = 1` 存入上下文。第二句是验证（`verify`）：它读取当前上下文，检查 `a + 1 = 2` 的良定义性，沿着 `a = 1` 做透明定义化简，再使用数值规范化规则。通过后，第二条事实进入当前上下文，成为后续语句可以继续使用的基础。

下面是这片代码的执行结果。

<details>
<summary><strong>展开查看：Litex执行结果</strong></summary>

```json
{
  "kind": "run",
  "success": true,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": true,
      "statement": "let a = 1",
      "proof_method": { "type": "define_obj" },
      "stores": ["a = 1"],
      "infers": []
    },
    {
      "success": true,
      "statement": "a + 1 = 2",
      "proof_method": {
        "type": "builtin_rule",
        "rule_name": "Calculation",
        "message": "Both sides evaluate to the same number"
      },
      "stores": ["a + 1 = 2"],
      "infers": []
    }
  ]
}
```

</details>

第二句经过良定义性、定义化简与数值检查；上面的 Normal JSON 只显示顶层的 `Calculation`，并未展开每个内部子步骤。读者可从这份日常记录直接回答几个问题：

| 读者想知道什么 | 在记录里看哪里 |
| --- | --- |
| 跑了哪一句 | `statement` |
| 是否成功 | 语句的 `success`，以及整次运行的 `success` / `session_error` |
| 为什么成立 | `proof_method`（规则名、引用、定义路径等） |
| 为什么停下 | `why_failed.phase` 与 `why_failed.goal` |
| 什么进入了后续上下文 | `stores` 与 `infers` |

Normal JSON 是面向人与工具的摘要。完整的 verify/exec 证据树不是日常 `-e` / `-f` / `-r` 打印的内容；未来若要交给 Lean 复核，还须把其中受支持的验证路径翻译为没有证明空洞的 Lean 证据。

良定义性先于事实接受：`1 / 0 = 1 / 0` 即使两边形式相同，也因分母为零而不能成为已接受的等式。

<details>
<summary><strong>展开查看：Litex执行结果</strong></summary>

当我们输入 `1 = 0` 时，Litex 的 Normal JSON 输出是

```json
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": false,
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

这份记录让人查看本步依据，让 AI 获得可据以修改的反馈，也能为定义与事实的依赖图提供材料。对照源码、已经建立的定义与事实，以及本步的验证方法，读者可以追问这一步为何成立、前后思路怎样衔接。第 4 节讨论协作流程；第 5 节讨论将受支持的内部证据交给 Lean 独立复核的目标。两者都建立在这里的逐句接受与明确停止边界上。

![Litex 事实关系图示例](https://litexlang.com/_next/image?url=%2Fassets%2Fknowledge_graph.png&w=640&q=75)


<details>
<summary><strong>小结：Litex 的设计体现了它的哪些数学观</strong></summary>

定义建立对象与词汇，验证确认事实，已接受的语句扩展后文的可用背景。这两个动作持续往返。Litex 希望由少量可组合的对象、关系、逻辑结构、规则和标准库承担常见数学，而非为每种表述增设孤立接口；覆盖程度仍在扩展与审计。

这种组合能否减少人和 AI 构造、理解及修复可检查知识的成本，是要靠实际任务检验的设计假设。输出依据的目的，是让读者在阅读源码之外，还能追问每一步的数学理由。

</details>

<details>
<summary><strong>实现摘要：记录如何生成</strong></summary>

当前实现把语句执行与结果记录连接起来；后续 Lean 路径仍是目标：

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
  → 后续集成目标：把支持范围内的证据交给 Lean 编译器和内核
```

JSON 直接从内部执行结果生成，呈现本步检查的摘要。关系图提供另一种查看方式；Lean 独立复核仍是尚待接入的目标。

</details>

<a id="set-theory"></a>

## 2. 从熟悉的数学世界开始：Litex 的集合论基础

_“语言设计，是宏大思想与繁琐细节的一种奇妙混合。”_

_— Bjarne Stroustrup_

Litex 以集合论为数学基础，用集合、元素、函数和关系组织数学。源码可以直接写下成员关系、子集关系、函数应用和等式，无须先展开常见对象的具体集合论构造。这种写法的目标，是让读者沿用熟悉的数学概念，降低理解形式化表示的额外成本。内置规则和数系接口如何对应基础理论，仍须逐项说明和审查。

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

对象能力的查找使用该对象规范身份下存储的事实。执行环境的 `special_properties` 索引保存实际的成员关系与等式事实，也包含对象命名后新得到的事实。函数调用检查从这些事实中读取签名；函数体展开沿已存储的等式查找并引用依据。例如，先写 `have fn f(x R) R = x + 1`，再写 `let g = f`，便支持直接验证 `g(4) = 5`。仅有成员事实 `g $in fn(x R) R` 则提供可调用性，并不确定具体函数值。由定义选定的默认结构字段视图仍属于单独的注解。

这不等于取消静态约束或推断。Litex 在接受表达式前仍会检查定义域、返回集合、结构字段和其他良定义性义务，并通过专用规则在证明中推出成员与载体事实。区别在于，这种推断向上下文增加 `e $in S` 一类事实，而不是推断一个决定对象身份的特权类型 `e : T`。

Lean 以依赖类型论为核心；Litex 选择以集合与成员事实组织用户层数学。Lean 的 `Set α` 同样能表达集合论，Mathlib 也提供丰富的数学接口；差异在于两者默认让作者怎样引入对象、陈述事实和交代验证依据。Litex 当前的覆盖仍在扩展，不能由共同的数学目标推出两者现有的表达范围相同。Litex 的验证器与内置规则构成自己的可信实现面，因此把证据交给 Lean 独立复核是一条重要的目标路线；早期编译实验尚未接入当前构建。

</details>

<a id="design-difficulty"></a>

### 2.1 设计难处：把具体的数学写法做成工作语言

“更具体”说的是作者通常直接使用的数学词汇。[Lean 的语言参考](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)说明，Lean 表层语法精化为核心类型论表达式，并由内核检查证明；可执行程序的编译器 IR 是另一条路径。Lean 也有丰富的记号与自动化。Litex 则选择用集合、成员事实和具名函数组织日常书写。

例如，`have a R = 2` 看起来只是一句话，当前 CLI 却分别记录 `a $in R` 与 `a = 2`，供后面的良定义性检查、计算和等式对齐使用。一个对象可有多个成员事实，别名还会影响函数签名的查找。作者少写一步操作，语言就必须替他维护这些跨语句关系，并在接受下一句前检查它们是否足以支持该句。

设计的难点在于让数值计算、集合构造、函数、关系、量词、见证、反证与归纳协同工作。康托尔证明中的 `{x X: not x $in f(x)}` 同时涉及受限集合构造、函数应用、否定与成员关系。每一种组合都要回答：表达式何时良定义、可以引用哪些前提、如何控制重复搜索、成功后存入什么事实与依据、失败时停在哪里。当前验证器给规则前提逐级降低查找权限；执行语句时先在临时环境检查，失败不把候选事实合并进上下文。这些机制共同支撑了较简洁的写法。

Litex 仍把关键构造、中间结论和见证交给作者，并提供 `claim`、`witness`、`by contra`、归纳等显式结构。它争取的是严格检查、常见构件的实际组合覆盖和易用性同时成立；任何单一例子或记号列表都不能证明“任意证明已经支持”。覆盖程度和未来的 Lean 独立复核须分别用验证结果与编译证据检验。

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

Litex 面向用户的命题语言大体具有一阶逻辑风格：原子关系或具名谓词通过受限的经典逻辑形式和量词组织。它偏好规范事实形态，命题和证明不能作为普通一等值任意组合——因此也不允许 `forall p prop` 一类对命题的量化；第 1 节说明这如何使事实表能按谓词名索引。这只描述命题接口；验证器还会检查良定义性，并从定义、上下文和受支持规则中寻找依据。

在这个背景下，Litex 的问题更具体地落在面向用户的对象接口上：
一套小型、以成员关系为中心的集合论式表层，能否在不要求用户先管理类型
宇宙（universe）的前提下，覆盖有实质内容的数学？

</details>

<a id="bottom-up"></a>

## 3. 让已建立的知识继续生长：自下而上的证明

_“如果我看得更远，那是因为我站在巨人的肩上。”_

_— Isaac Newton，致 Robert Hooke 的信（1676）_

在 Litex 中，证明通常从已有的条件和事实向前推进。每一个通过验证的步骤都会留下后面可以使用的知识。即使最终目标尚未完成，已经建立的中间结论也可以继续使用。

Lean 的典型 tactic 交互先给出目标，再把它化为子目标。这里比较的是写作与交互的默认方向：Litex 常问“已知事实还支持什么”，Lean tactic 常问“当前目标还需什么”；两者都须严格检查所得结论。

<a id="two-directions"></a>

<details>
<summary><strong>小例子：同一条代数等式的自上而下与自下而上写法</strong></summary>

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

Mizar、Isar、ACL2 和 Naproche 已支持前向文本、定理累积或逐步检查，因此“自下而上”并非 Litex 独有。Litex 检验的是组合：普通事实自动触发局部验证，通过后扩展上下文，同时让已接受或停下来的路径保持可见，供用户或人工智能检查和修复；只有常规验证不足时才写显式证明结构。更完整的比较见第 1 节的小结“Litex 与 Naproche——相近目标，不同核心接口”。

</details>

<a id="interaction-loop"></a>

## 4. 人、AI 与 Litex 共同推进证明

_“所谓增强人的智力，就是增强人面对复杂问题的能力……”_

_— Douglas Engelbart，《增强人类智力：概念框架》（1962），引言（节选）_

人负责数学问题、关键构造与最终判断；AI 提出或修订下一段源码；Litex 检查该段并返回依据或停止位置。已接受的语句成为下一段的背景，失败语句则留给人或外部工具记录和修复。这是逐句验证结果进入协作流程的方式：

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
   └─ RolledBack
         → 基于证据的诊断
         → 修复同一个片段，再试
                         ↓
全部成功片段按顺序衔接 → 问题得到解决与形式化
                         ↓
人类专家做基本校验
                         ↓
这些 Litex 代码成为后续其他问题的基石
```

每轮只处理一个定义、定理或小证明片段。通过检查的片段成为后续证明的依据，失败尝试不会改变已有的数学上下文。如果协作工具保存候选源码及其输出，人和 AI 就能回看修复过程；完整的尝试记录由这些工具维护。全部片段通过后，人还须核对形式陈述是否忠实于原题与数学意图。

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
            abs(s(n) - a) < epsilon

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
  "success": false,
  "detail": "normal",
  "session_error": null,
  "statement_results": [
    {
      "success": false,
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
        abs(c) + 1 > 0
        epsilon / (abs(c) + 1) $in R+
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / (abs(c) + 1), K)}
        witness exist K N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, K)} from N0:
            forall n N:
                n >= N0
                =>:
                    abs(s(n) - a) < epsilon / (abs(c) + 1)
                    abs(c * s(n) - c * a) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < epsilon
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
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

## 5. 连接 Lean 独立复核，并与 Mathlib 兼容（Experimental）

_“形式证明的每一步逻辑推导，都已被检查直至数学的基础公理。”_

_— Thomas Hales，《Formal Proof》（2008）_

Litex 当前使用自己的验证器检查源码并提供反馈；把证明交给 Lean 独立复核，是下一阶段的目标。这需要满足三个条件：翻译保持原命题的含义，生成的证明没有空洞，而且确实通过 Lean 内核检查。满足这些条件后，才能减少对 Litex 验证器本身的依赖，并进一步连接 Mathlib。早期编译实验的产物仍被保留，但当前构建尚未接入编译器。

> **当前构建：** `litex` 可执行程序没有集成的编译入口。早期实验保留的脚本指向本构建不提供的二进制目标。下面仅记录那次实验；它尚未由当前构建重新生成，也未在当前 Lean 环境中重新核验。

<details>
<summary><strong>示例：Litex代码如何编译成Lean</strong></summary>

目标中的 Litex–Lean–Mathlib 路径依次经过：

`Litex 源码 → Litex 验证 → ToLean 编译 → Lean 内核复核 → 手写 adapter → Mathlib 定理`

> 当前验证结果保留事实与规则的来源；编译器未来须把每条**受支持**的接受路径变成 Lean 可检查的证据，并明确拒绝尚未覆盖的路径。规则数量本身不能代替这项逐路径的语义工作。

举例：我们想要证明前`n`个正奇数之和是`n^2`。我们先写下Litex的源码：

> **迁移示例：** 当前 `src/` 检查停在 `internal_bug: name n is already bound in an enclosing parse scope`；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
have fn kth_odd(k Z) Z = 2 * k - 1

forall n Z:
    n >= 1
    =>:
        sum(1, n, kth_odd) $in Z

forall n Z:
    n^2 $in Z

thm sum_first_odds: 
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ? sum(1, n, kth_odd) = n^2

        ? from n = 1:
            kth_odd(1) = 2 * 1 - 1 = 1
            sum(1, 1, kth_odd) = kth_odd(1) = 2 * 1 - 1 = 1 = 1^2

        ? induc:
            kth_odd(n + 1) = 2 * (n + 1) - 1
            sum(1, n + 1, kth_odd) = sum(1, n, kth_odd) + kth_odd(n + 1) = n^2 + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2
```

编译到Lean（不同的Litex版本编译出来的东西可能会不同）

```lean
-- Generated by StmtResultToLeanCompiler from main.lit. DO NOT EDIT.
import Litex

set_option linter.style.nameCheck false

namespace __Compiler_main

noncomputable def kth_odd : Litex.Fn Litex.Z Litex.Z :=
  { call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) }

theorem __fact0 : Litex.In kth_odd (Litex.fnSet Litex.Z Litex.Z) := by
  exact Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd

theorem __fact1 : Litex.Same kth_odd ({ call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) } : Litex.Fn Litex.Z Litex.Z) := by
  unfold kth_odd
  exact Litex.Same.refl ({ call := fun {__alpha} (__arg : __alpha) __arg_in => (((2 : ℤ) * Litex.In.rep __arg __arg_in) - (1 : ℤ)), callOwn := fun (__arg : ℤ) => (((2 : ℤ) * __arg) - (1 : ℤ)) } : Litex.Fn Litex.Z Litex.Z)

theorem __fact2 :
    ∀ (__p1 : ℤ) (__domain1 : Litex.Le (1 : ℂ) (((__p1) : ℂ))), Litex.In (Litex.sum (1 : ℤ) __p1 kth_odd) Litex.Z := by
  intro n __domain_f17
  have __infer2_0 : Litex.Lt (0 : ℂ) (((n) : ℂ)) := Litex.Lt.transLe (Litex.OrderBridge.ltOfComplexReals (show (0 : ℝ) < (1 : ℝ) by norm_num)) (__domain_f17)
  have __prior2_0 : Litex.In (Litex.sum (1 : ℤ) n kth_odd) Litex.Z := Litex.In.own Litex.Z ((Litex.sum (1 : ℤ) n kth_odd))
  exact __prior2_0

theorem __fact3 :
    ∀ (__p1 : ℤ), Litex.In (((((__p1) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) Litex.Z := by
  intro n
  have __prior3_0 : Litex.In (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) Litex.Z := Litex.Rules.complexIntPowNatInZ (n) (2 : ℕ)
  exact __prior3_0

theorem sum_first_odds :
    ∀ (n : ℤ) (__domain_f48 : Litex.Le (1 : ℂ) (((n) : ℂ))),
      Litex.Same (Litex.sum (1 : ℤ) n kth_odd) (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := by
  intro n __domain_f48
  have __step4_29 : ∀ (__p1 : ℤ) (__domain1 : Litex.Le (1 : ℂ) (((__p1) : ℂ))), Litex.Same (Litex.sum (1 : ℤ) __p1 kth_odd) (((((__p1) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := by
    intro __target_value __domain1
    have __target_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__target_value : ℝ) := by
      simpa [Litex.Le, Litex.OrderValue] using __domain1
    have __target_ge_start : (1 : ℤ) ≤ __target_value := by
      exact_mod_cast __target_ge_start_real
    exact Litex.Rules.integerInductionFrom (motive := fun __induction_value : ℤ => Litex.Same (Litex.sum (1 : ℤ) __induction_value kth_odd) (((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) (by
    have __step4_2 : (Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))) ∧ (Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (1 : ℂ)) := by
      exact ⟨Litex.Same.trans ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((1 : ℤ))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num)))) (Litex.Same.refl (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))), Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])⟩
    have __infer4_3 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (1 : ℂ) := Litex.Same.trans ((__step4_2).1) ((__step4_2).2)
    have __step4_4 : (Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ))) ∧ (Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ))) ∧ (Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (1 : ℂ)) ∧ (Litex.Same (1 : ℂ) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) := by
      exact ⟨Litex.Same.trans (Litex.Same.symm (Litex.Same.symm (Litex.Same.trans (Litex.Rules.integerRangeSumSingleOwn (1 : ℤ) kth_odd) ((__step4_2).1)))) (Litex.Same.symm ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((1 : ℤ))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num))))), ⟨(__step4_2).1, ⟨(__step4_2).2, Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])⟩⟩⟩
    have __infer4_5 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) := Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)
    have __infer4_6 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (1 : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)) ((__step4_4).2.2.1)
    have __infer4_7 : Litex.Same (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans (Litex.Same.trans ((__step4_4).1) ((__step4_4).2.1)) ((__step4_4).2.2.1)) ((__step4_4).2.2.2)
    have __infer4_8 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_4).2.1) ((__step4_4).2.2.1)) ((__step4_4).2.2.2)
    have __infer4_9 : Litex.Same (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans ((__step4_4).2.2.1) ((__step4_4).2.2.2)
    have __infer4_10 : Litex.In (1 : ℂ) Litex.RPos := (Litex.In.congr ((__step4_4).2.2.2) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_11 : Litex.Positive (1 : ℂ) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_10)))
    have __infer4_12 : Litex.In (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) Litex.RPos := (Litex.In.congr (__infer4_7) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_13 : Litex.Positive (Litex.sum (1 : ℤ) (1 : ℤ) kth_odd) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_12)))
    have __infer4_14 : Litex.In (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) Litex.RPos := (Litex.In.congr (__infer4_8) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_15 : Litex.Positive (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (1 : ℤ)) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_14)))
    have __infer4_16 : Litex.In (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) Litex.RPos := (Litex.In.congr (__infer4_9) Litex.RPos).mpr (Litex.Rules.complexEqRealInRPos (((1 : ℚ) ^ (2 : ℤ) : ℚ) : ℂ) (1 : ℝ) (by norm_num) (by norm_num))
    have __infer4_17 : Litex.Positive (((2 : ℂ) * (1 : ℂ)) - (1 : ℂ)) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_16)))
    exact (by simpa using (__infer4_7))) (fun (__induction_value : ℤ) (__induction_ge_start : (1 : ℤ) ≤ __induction_value) (__induction_hypotheses : Litex.Same (Litex.sum (1 : ℤ) __induction_value kth_odd) (((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) => by
    have __infer4_18 : Litex.Lt (0 : ℂ) (((__induction_value) : ℂ)) := Litex.Lt.transLe (Litex.OrderBridge.ltOfComplexReals (show (0 : ℝ) < (1 : ℝ) by norm_num)) ((by
      have __induction_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__induction_value : ℝ) := by
        exact_mod_cast __induction_ge_start
      simpa [Litex.Le, Litex.OrderValue] using __induction_ge_start_real))
    have __infer4_19 : Litex.In (Litex.sum (1 : ℤ) __induction_value kth_odd) Litex.RPos := (Litex.In.congr (__induction_hypotheses) Litex.RPos).mpr (Litex.Rules.positiveIntegerRationalPowInRPos (__induction_value) (2 : ℤ) (__infer4_18) (by norm_num))
    have __infer4_20 : Litex.Positive (Litex.sum (1 : ℤ) __induction_value kth_odd) := (by simpa [Litex.In.rep] using (Litex.Rules.positiveOfInRPos (__infer4_19)))
    have __step4_21 : Litex.Same (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))) (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)) := by
      exact Litex.Same.trans ((by
      unfold Litex.fnApplyCarrier kth_odd
      exact Litex.Same.intSubComplex (Litex.Same.intMulComplex (Litex.Same.intComplexOfEq (z := (2 : ℤ)) (by norm_num)) (Litex.Same.intComplexOfEq (z := ((__induction_value + (1 : ℤ)))) (by norm_cast))) (Litex.Same.intComplexOfEq (z := (1 : ℤ)) (by norm_num)))) (Litex.Same.refl (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)))
    have __step4_22 : (Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))) ∧ (Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))) ∧ (Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ)))) ∧ (Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)) := by
      exact ⟨Litex.Rules.integerRangeSumSplitLastOwn (1 : ℤ) __induction_value kth_odd ((by simpa [Litex.Le, Litex.OrderValue] using ((by
      have __induction_ge_start_real : (((1 : ℤ)) : ℝ) ≤ (__induction_value : ℝ) := by
        exact_mod_cast __induction_ge_start
      simpa [Litex.Le, Litex.OrderValue] using __induction_ge_start_real)))), ⟨Litex.Same.intCastAddComplex (__induction_hypotheses) (Litex.Same.intComplex ((Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ))))), ⟨Litex.Same.addCongrRightInt (Litex.Same.refl ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ))) (__step4_21), Litex.Same.trans (Litex.Same.refl (((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))))) (Litex.Same.trans (Litex.Same.ofEq ((show ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) = ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) from (by norm_cast <;> ring_nf)))) (Litex.Same.symm (Litex.Same.refl (((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ)))))⟩⟩⟩
    have __infer4_23 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) := Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)
    have __infer4_24 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) := Litex.Same.trans (Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)) ((__step4_22).2.2.1)
    have __infer4_25 : Litex.Same (Litex.sum (1 : ℤ) (__induction_value + (1 : ℤ)) kth_odd) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans (Litex.Same.trans ((__step4_22).1) ((__step4_22).2.1)) ((__step4_22).2.2.1)) ((__step4_22).2.2.2)
    have __infer4_26 : Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (((2 : ℂ) * ((((__induction_value) : ℂ)) + (1 : ℂ))) - (1 : ℂ))) := Litex.Same.trans ((__step4_22).2.1) ((__step4_22).2.2.1)
    have __infer4_27 : Litex.Same ((((Litex.sum (1 : ℤ) __induction_value kth_odd) : ℤ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans (Litex.Same.trans ((__step4_22).2.1) ((__step4_22).2.2.1)) ((__step4_22).2.2.2)
    have __infer4_28 : Litex.Same ((((((__induction_value) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) + (Litex.fnApplyCarrier (domain := Litex.Z) (codomain := Litex.Z) kth_odd ((Litex.In.own (Litex.fnSet Litex.Z Litex.Z) kth_odd)) (__induction_value + (1 : ℤ)))) ((((((__induction_value) : ℚ)) + (1 : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := Litex.Same.trans ((__step4_22).2.2.1) ((__step4_22).2.2.2)
    exact (by simpa using (__infer4_25))) __target_value __target_ge_start
  have __c4_0 : Litex.Same (Litex.sum (1 : ℤ) n kth_odd) (((((n) : ℚ)) ^ (2 : ℤ) : ℚ) : ℂ) := (by
    simpa [Litex.In.rep, Litex.fnApply, Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using (__step4_29 n (by
    simpa [Litex.In.rep, Litex.fnApply, Litex.fnApplyOwn, Litex.abs, Complex.ext_iff, Real.norm_eq_abs] using (__domain_f48))))
  exact __c4_0

end __Compiler_main

```

生成的代码是Lean代码，但是是在Litex的语义下的Lean代码。我们稍加一个adapter，将 Litex 的表示桥接到 Mathlib：

```lean
import Generated

/-! The handwritten interface from generated Litex evidence to native Mathlib. -/

namespace Adapter

/-- Export the generated theorem as ordinary Mathlib equality. -/
theorem sumFirstOddsNative
    (n : ℤ)
    (oneLeN : (1 : ℤ) ≤ n) :
    ∑ k ∈ Finset.Icc (1 : ℤ) n, (2 * k - 1) = n ^ 2 := by
  have generated :=
    __Compiler_main.sum_first_odds n
      (Litex.OrderBridge.leOfComplexReals (by exact_mod_cast oneLeN))
  have exactComplexEq :
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
        ((n ^ 2 : ℤ) : ℂ) := by
    calc
      ((Litex.sum (1 : ℤ) n __Compiler_main.kth_odd : ℤ) : ℂ) =
          ((((n : ℚ) ^ (2 : ℤ) : ℚ) : ℂ)) :=
        Litex.Same.intComplexEq generated
      _ = ((n ^ 2 : ℤ) : ℂ) := by norm_cast
  exact_mod_cast exactComplexEq

end Adapter

```

桥接完成后，结论可以使用 Mathlib 的原生接口：

```lean
import Adapter

/-- A native theorem whose statement is entirely independent of Litex. -/
theorem firstHundredPositiveOddIntegersSum :
    ∑ k ∈ Finset.Icc (1 : ℤ) 100, (2 * k - 1) = 10000 := by
  exact Adapter.sumFirstOddsNative 100 (by norm_num)

```

这份早期产物说明交接大致需要哪些表示与 adapter；它不是当前 `src/` 已能生成同一证明的证据。正式接入时，仍要逐项检验命题保持、规则覆盖和 Lean 内核结果。

</details>

<a id="ecosystem-role"></a>

## 6. 从语言到生态：Litex 想扮演什么角色

_“预测未来最好的方式，就是创造未来。”_

_— Alan Kay，《The Early History of Smalltalk》（1993）_

Litex 希望让同一份经过验证的源码和结果，用于人的阅读、AI 的修复、知识关系的整理，以及未来的 Lean 复核。下面列出这些生态建设的目标：

| 生态角色 | Litex 希望产生的实际成果 |
| --- | --- |
| 可读推理的前端 | 人可以直接审核的数学对象、条件、中间事实和结论 |
| 可信推理数据的生产层 | 经过机器检查的事实与验证来源、明确的停止边界，以及被显式标出的可信边界 |
| 现有生态的接入层 | 从一开始的设计上即面向 Lean 编译与复核（第 5 节，Experimental）；早期 Lean 产物仅记录实验覆盖，当前 `src/` 未接入编译器；以及明确分离、由 AI 或人类编写的新增 Lean/Mathlib adapter |
| 证明 → 可执行代码（Experimental） | 把已检查的计算片段转化成可运行的 Python / C（第 6.1 节） |

当前验证器与工具已具备相当规模，但可用性、领域覆盖与实际采用仍须由带日期的例子和使用结果证明。对这些方向感兴趣，可以联系 litexlang@outlook.com。

<details>
<summary><strong>Litex的生态位</strong></summary>

这条路线有一个规模矛盾：对象、事实、证明与可信边界需要少数设计者持续统筹，才能保持语义一致；实现却涉及大量规则、良定义性路径、证据结果、失败诊断、例子和测试。以 2026 年 10 月 4 日工作树中的已跟踪文件计，当前 `src/` 有 631 个 Rust 文件、约 13.7 万物理行。全仓库的 Rust 文件约 41.9 万行，但其中包含 `scripts/` 下的历史与实验实现，不能都算作当前验证器。这些数字说明工程规模，不证明数学覆盖或正确性。

AI 工具改变的是小团队编写、检查和迭代大量实现工作的成本；它不替人决定数学语义、可信边界或验收标准。集合论式语言、自然可读的证明和局部自动化也各有先例。Litex 要检验的是：把这些选择放进同一个默认工作界面，在新的工程条件下能否形成可读、可检查、可持续扩展的数学工作流。

</details>

<a id="executable-code"></a>

### 6.1 把证明编译成可执行代码（Python / C）（Experimental）

Litex 还在实验把已验证的计算片段转化成可运行的 Python 或 C。目前主要处理支持范围内的数值定义与 `algo` 片段，让同一份经过检查的计算写法也能用于执行。

这条路线刻意做窄，且标明实验性。它不是整门 Litex 到 Python/C 的编译器；覆盖限于可抽取定义。命令行见 CLI 文档中的 `-extractpython` / `-extractc`。

<details>
<summary><strong>示意：牛顿法逼近 √2 的单步 → Python / C</strong></summary>

同一份用于科学计算的 Litex 证明，可以转化成可执行代码。例如牛顿法逼近 √2 的单步更新：

> **迁移示例：** 当前 `src/` 检查停在 `parse_error: undefined name newton_sqrt_two_step`；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
```litex
have fn newton_sqrt_two(x R+) R+ = (x + 2 / x) / 2

claim:
    ? forall x R+:
        newton_sqrt_two_step(x) = newton_sqrt_two(x)
    newton_sqrt_two_step(x) = (x + 2 / x) / 2 = newton_sqrt_two(x)

algo newton_sqrt_two_step(x R) R by cases:
    case x = 0: 1
    case x != 0: (x + 2 / x) / 2
```

转化为 Python：

```python
def newton_sqrt_two_step(x):
    if x == 0.0:
        return 1.0
    elif x != 0.0:
        return ((x + (2.0 / x)) / 2.0)
    raise AssertionError("unreachable verified Litex cases")
```

转化为 C：

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

</details>

<a id="reasoning-direction"></a>

<a id="conclusions"></a>

## 7. 追寻与众不同的艺术

_“数学家像画家或诗人一样，是模式的创造者。”_

_— G. H. Hardy，《一个数学家的辩白》（1940）_

<!-- 这一段比较理想主义一点。因为AI时代大家过度关注实用主义了，容易忽略一个原生的、创新的、与众不同的新解决方案带来的长期的影响力。不管是数学界，还是任何科学，大家都鼓励对同一问题的不同角度、不同解决方案的出现。这样的不同的观点，往往才是科学史上真正突破的来源，最终可能会带来更大的效益提高。 -->

数学需要可信的结论，也需要让人读懂结论如何建立的语言。Litex 因此提出一个可检验的问题：以集合和事实组织源码，自动检查受支持的局部步骤，并记录每一步的依据，能否降低人和 AI 构造、审阅、修复可检查数学的成本？这条路线值得与 Lean、Mizar、Naproche 等已有道路并行探索，用真实数学任务检验它的效果。

我希望 Litex 帮助更多人在参与严格验证的同时，继续理解数学、创造数学。当前的代码、例子和边界是这项探索的起点；以后能否覆盖更多领域、交给 Lean 独立复核、真正减轻人的负担，仍须逐一证明。

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

注：当前仓库同时保留已检查成果、实验和未完成工作。*公开可见不等于宣称完成*；能力应以测试、带日期的状态、可信边界和已知限制为准。

### 原生定理接口与诊断（2026-10-02）

25 个保留的旧定理名称现在在当前验证器中有原生接口约定。定理应用流程在将结论写入周围上下文之前，检查前提与结论的良定义性，并报告实际失败的阶段和前提。含有 `i` 的复数算术由计算处理；索引构造要求索引集非空。这些改动保留了 AST 与 Runtime/ExecEnv 的接口约定；定义端点仍通过显式等式链对齐。支持的参数形式因定理而异；依赖选择公理的积集非空结论会标明其选择公理来源。

<a id="overview-readers"></a>

## 附录：编程、数学与Litex形式化

这一节从 Lean 用户、数学从业者、程序员和其他知识领域读者的经验出发，讨论 Litex 可能带来的知识与视角。您可以选择感兴趣的部分阅读，也可以回到[五条主线](#overview-spine)继续了解语言设计。

### 写给 Lean 用户

为什么还要另一种形式化语言？

我第一次看到 Lean 时，十分震惊：数学居然可以写成代码，证明居然可以交给机器检查！“数学代码化”这个想法本身就让我感到兴奋，也让我开始思考自己希望怎样使用一门形式化语言。

学习过程中，我渐渐有了几个问题。What if，我能直接写下 `1 + 1 = 2`，不用先写 `example`，再接一个 `by ...`？What if，定义了奇数以后，我直接写 `$odd(13)`，语言就能按定义检查它？What if，已经知道“所有人都会死”和“苏格拉底是人”，我就能直接写“苏格拉底会死”，不用再点名引用那条全称前提？

这些问题汇成一个具体的界面选择：作者决定数学上的下一步，语言寻找受支持的局部依据，并说明这一步给上下文留下什么。代价是验证器须承担良定义性、依据匹配、结果记录与失败定位；第 2.1 节已展开这项设计责任。Lean 用户可以据此判断，自己得到的是另一种默认工作流，而不只是几处较短的记号。

```text
Lean:  命题 → 证明目标 → tactic 精化 → 证明项 → 内核检查
Litex: 对象与事实 → 内核检查并检索依据 → 已验证事实扩展上下文
```

Lean 把对象、命题和证明纳入依赖类型论的 term/type 体系；Litex 在源码中区分数学对象、事实以及定义和证明步骤。下面的 subtype 对照展示：当函数调用的条件已经成立时，两种语言怎样写出这个调用。这里比较的是表达方式和阅读成本。

Lean 仍是 Litex 的重要参照与未来复核目标。Lean 的证明经精化成为由内核检查的证明项；面向可执行程序的编译器 IR 是另一条路径。Litex 的早期编译实验留下了 Lean 产物，但当前 `src/` 尚未接入编译器。性能或学习成本上的优势也不能只凭界面推断，须在可比任务上测量。

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
<summary><strong>个人思考：Litex补齐了AI推理的范式缺口？</strong></summary>

从前提出发积累中间事实，与从目标出发分解证明义务，都是数学工作中有用的方向。Litex 的默认源码偏向前者；Lean tactic 的常见交互偏向后者。AI 究竟在哪一种表示下更容易提出正确步骤、利用失败反馈和复用中间结论，是可以比较的研究问题，不能仅从训练方式推断。

理想的协作流程可以同时利用两种方向：先用目标选择有价值的路线，再逐句积累可检查的事实。Litex 与 Lean 若能完成可信交接，就可能把两种工作方式连接起来；当前编译入口尚待实现。

</details>

### 写给数学从业者

如果您从事数学，您可能首先关心的不是又一种工具，而是数学理解和数学代表的传统价值观在 AI 时代如何被保留。

AI 正在带来“推理丰盈”：答案与证明可以大规模生成，却不自动可信、可解释，也不必然加深理解。正如[陶哲轩在 2026 年 ICM 公开讲演](https://www.youtube.com/watch?v=M0--ZH1lOzg)所说，数学的未来更需转向证明的验证、阐释与消化。更普遍的问题是：如何把 AI 生成的推理变成可检查、可理解、可复用的共同知识——这不只关乎数学，也关乎各行业的知识生产。

今天的数学圈并不平静：热点轮换很快，AI 让数学问题有时像「挖矿」一样被追逐。就在2026年9月，陶哲轩等25位菲尔兹奖得主警告：AI公司把“快速解题”当作数学进步指标，可能牺牲真正的理解、原创性、学术传承与归属规范，导致AI发展目标与数学共同体严重错位。[原文](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/)

Litex 想在日常数学表达与形式化验证之间建立可读的工作界面：让领域知识可以明确写成对象、条件与事实，交给机器检查，再回头理解每一步使用的依据。数学价值不只在于得到结论，也在于理解结论怎样成立。

Litex 在源码中分别写清数学对象、关于它们的事实，以及定义和证明步骤，让读者可以沿着熟悉的数学思路阅读。这样的区分首先服务于表达和理解；证明是否容易完成，还取决于具体问题与系统支持。

数学家最能判断一种新写法是否忠实于数学意图。Litex 想请教的，不只是某条证明能否通过，还包括源码、验证依据和可复用接口是否有助于理解数学。作者希望以这种语言探索为 Math for AI 提供一种新视角，也欢迎读者用真实数学问题检验它。

<a id="reader-programmers"></a>

### 写给程序员

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

事实表与规则表把一部分依据检索工作从作者转移给语言；[第 1 节](#fact-oriented)说明这条默认路径的搜索边界，[验证实现的分工](#automation-implementation)解释相应的工程成本。作者能少写许多操作，是因为每条受支持的路径都在实现中处理了前提、结果与失败反馈。

还有第二条程序员常关心的实验性编译路线：计算片段在 Litex 里检查过之后，可以尝试抽出可运行的 Python 或 C（第 6.1 节）——同样标明实验性，且范围很窄，不是整门语言的后端。

### 写给其他知识领域的读者

在数学之外，Litex 希望用简单的语法表达对象、关系、条件与规则，再用清晰的验证反馈，邀请我们探索人类直觉、机器验证与数学知识之间的另一种表现形式。Litex 也希望探索形式化语言在真实知识工作中的入口：从 AI 安全、AI 输出可解释性、金融风控、精密软件工程，到物理、化学、医疗、法律和工程。

这些目前是探索方向，不是对相关行业已有支持的声明。欢迎更多非数学专业背景的工作者参与探索：在自己的行业中使用形式化工具，理解依据、发现冲突、预防错误。

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

> **迁移示例：** 当前 `src/` 检查停在 `by_contra` (`by contradiction`)；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
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

> **迁移示例：** 当前 `src/` 检查停在 `internal_bug: name n is already bound in an enclosing parse scope`；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
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

> **迁移示例：** 当前 `src/` 检查停在 `search_proof` (`p.first = 1`)；以下保留写法不算已验证结果。

<!-- litex:skip-test -->
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
