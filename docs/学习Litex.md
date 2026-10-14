# 学习 Litex：从一条可检查的事实到你自己的数学文件

官网页面: https://litexlang.com/doc/学习Litex

英文版: https://litexlang.com/doc/Learn_Litex

先写 `1 + 1 = 2`，把它检查通过，再把同样的习惯扩展成定义和证明。本课程带你走过在 Litex 中做一小段数学发展所需的决定：对象是什么、在哪里定义、已知什么、还需要证明什么。

> **Litex 适合与 AI 交互：提出数学步骤、检查、读取反馈，再修正或继续。开启 `-session` 并保持同一个进程，普通失败保留此前已接受的定义和事实。不要每加几条新代码就从头重跑。** 见[简单代码对照](#交互修复时保留已接受工作)。

你只需要基础算术与中学代数。不假定有编程或证明助手经验。主课程大约 **90 分钟**，可选扩展大约 **30 分钟**，已包含运行与改例子的时间。这些是学习估计，不是实测完成时间。

学完后，你应能：为函数写明合法输入、陈述一般性质、给出短证明、理解失败检查，并保存一份自洽的 `.lit` 文件。你也会看到这份已检查源码如何服务人类读者或 AI agent。

## 你的路线

| 部分 | 你将做成或理解什么 | 建议时间 |
| --- | --- | --- |
| [1. 检查你的第一条事实](#1-检查你的第一条事实) | 一条 Litex 能检查的数学句子 | 8 分钟 |
| [2. 给对象与性质命名](#2-给对象与性质命名) | 一个值、一个函数、一个性质 | 12 分钟 |
| [3. 把定义域写清楚](#3-把定义域写清楚) | 排除零的倒数 | 12 分钟 |
| [4. 从例子走到一般事实](#4-从例子走到一般事实) | 全称陈述与局部证明 | 15 分钟 |
| [5. 写跟随数学本身的证明](#5-写跟随数学本身的证明) | 展开定义、等式链与分情形 | 13 分钟 |
| [6. 读懂失败并做小修复](#6-读懂失败并做小修复) | 修正定义域，诚实阅读反馈 | 15 分钟 |
| [7. 完成你的第一份 lit 文件](#7-完成你的第一份-lit-文件) | 一份完整的已检查产物与下一步 | 15 分钟 |
| [可选扩展](#可选扩展) | 命名结果、存在性与 agent 循环 | 30 分钟 |

主课程后的数学练习，见 [Learn Math with Litex：数学例子](#learn-math-with-litex)。定义、证明和练习都直接放在本篇文档中。

按顺序读主课程。对每个例子：先预测它的含义，再运行，最后尝试建议的改动。若你在 GitHub 或下载的 Markdown 中阅读，说明与代码都在这里；课程不依赖特定网页界面。

每个 `litex` 代码块都是完整、独立的例子。切换到另一个独立例子时使用独立上下文，或另存为单独的 `.lit` 文件；在本地扩展或修复同一个例子时，保持同一个 `-session`。标为 `text` 的块表示有意失败、片段或会话记录；标题会说明是哪一种。不要在未修复的情况下把它们粘进一份本应通过的文件。

## 选择在哪里运行例子

在网站上，若 Litex 例子旁有编辑器就用它；否则把整块复制到 [在线 playground](https://litexlang.com)。改源码并运行检查。阅读课程或在线试这些小例子，不必先安装。

本地使用请先看 [安装指南](安装Litex.md)，再检查安装是否正常：

```bash
litex -version
litex -strict -e '1 + 1 = 2'
```

用英文输出对已保存文件做基线或最终检查：

```bash
litex -lang en -strict -f first.lit
```

本练习请把文件放在没有 `litex.config` 的新目录里，让每个文件独立运行。项目上下文会在可选扩展里介绍。[CLI 参考](Litex命令行参考.md) 说明与安装无关的命令细节。

## 1. 检查你的第一条事实

**问题：** $2(3+4)=14$ 成立吗？怎样把计算写下来，让别人也能检查同一句话？

```litex
1 + 1 = 2
2 * (3 + 4) = 14
3^2 = 9
```

这些行是**待检查的事实**。它们不是让 Litex 去搜答案，也不是打印表达式的值。你给出一句数学句子，例如 `3^2 = 9`，Litex 用已有规则与上下文去检查它。

`*` 表示乘法，`^` 表示乘方。`=` 陈述数学相等，不是给左边赋新值的命令。乘法要显式写出：用 `2 * x`，不要写 `2x`。

成功的批量检查在 JSON 结果里有 `"run_result": "success"`、`"session_terminated": false` 且 `"termination": null`。网站可能把结果呈现得更简单。交互式命令行 REPL 对成功输入块打印 `success`。第 6 部分会更仔细地读失败结果。

想直观看到 Litex 如何检查一条事实，可以看 [Litex 验证流程图](https://litexlang.com/assets/diagrams/litex-verification-pipeline-v1.png)。

**试一试：** 把第二行改成 `2 * (3 + 5) = 16`。运行前先预测结果。再故意把右边改成 `15`。

第一次改动应通过；第二次应失败。对这个具体计算，普通算术也能看出改后的等式为假。一般而言，Litex 检查失败需要更多解释，不只是“等式为假”。

**带走：** Litex 文件记录可被检查的数学陈述。你的第一件事，是精确说出你想检查什么。

## 2. 给对象与性质命名

下一步是说明符号的含义。数值名、可调用函数、性质，各自工作不同。

### 给具体值起名

**问题：** 若实数 `x` 是 2，能否用这个名字检查计算？

```litex
have x R = 2
x + 1 = 3
x^2 = 4
```

`have x R = 2` 引入 `x`，检查其值属于 `R`，并使 `x = 2` 可用。`R` 是实数集。后面的事实可以使用这些已检查信息。

同一符号继续表示同一数学对象。本课程不使用可变变量：接着写 `x = 3` 会要求一个与已选值不一致的等式。

对比一个**尚未选定具体值**的名字：

```litex
have x R
x + 0 = x
x $in R
```

这里 `x` 是任意实数。已知它属于 `R`，但不知道 `x = 2`。恒等式 `x + 0 = x` 对这个任意实数成立。

### 带定义方程的函数

**问题：** 一个实数到零的距离是什么？

数学定义是 $d(x)=|x|$：

```litex
have fn distance_from_zero(x R) R = |x|
distance_from_zero(-3) = distance_from_zero(3) = 3
```

第一行读作：“定义名为 `distance_from_zero` 的函数，实数输入 `x`，实数输出，值为 `|x|`。”`abs` 是绝对值。之后可以把名字作用到输入上，如 `distance_from_zero(-3)`。

第二行是等式链，要求两边相邻等式都成立：`-3` 处的距离等于 `3` 处的距离，且该距离等于 `3`。函数定义描述数学值；它们本身不承诺导出器能把每个定义变成 Python 程序。

### 带含义的性质

**问题：** 怎样命名“这个实数大于二”？

```litex
prop is_above_two(t R):
    t > 2

by def $is_above_two(3)
```

`prop` 引入命名性质。缩进体给出含义：`is_above_two(t)` 表示 `t > 2`。事实中的 `$` 标记性质应用。

声明性质并不证明它对每个输入成立。`by def $is_above_two(3)` 在 `3` 处检查定义条件，并折成命名性质。在 `1` 处，条件不成立。

| 你需要什么 | 这里用的形式 | 它贡献什么 |
| --- | --- | --- |
| 命名的值 | `have x R = 2` | 名字、隶属关系与值等式 |
| 任意实数对象 | `have x R` | 名字与隶属关系，无选定值 |
| 函数 | `have fn f(x R) R = ...` | 带定义方程的可调用值 |
| 性质 | `prop P(x R): ...` | 数学条件的名字 |
| 性质的一个实例 | `by def $P(value)` | 对该定义的一次已检查使用 |

**试一试：** 把距离例子里两个 `3` 输入都改成 `5`，并调整最后的值。再把 `is_above_two` 的输入从 `3` 改成 `1`。

**带走：** 对象是你谈论的东西。事实是关于这些对象的陈述。定义使含义可供后续检查使用。

## 3. 把定义域写清楚

在问事实是否成立之前，先检查：对你允许的输入，表达式是否有意义。

### 集合与隶属

```litex
0 $in N
-2 $in Z
1 / 2 $in R
2 $in {1, 2, 3}
```

`N` 是自然数集（含零）；`Z` 是整数集；`R` 是实数集。`$in` 表示“属于”。花括号如 `{1, 2, 3}` 描述有限展示集合。

同一对象可属于多个集合：`2` 既是自然数、整数，也是实数。写 `have x R` 或 `forall x R` 时，你引入一个属于 `R` 的数学对象，而不是把它变成编程语言里的浮点值。Litex 的 [对象模型](Litex手册.md#pure-set-object-model) 以集合为基础；对本课程的例子，按隶属关系理解就够了。

### 倒数需要合法输入

**问题：** 定义实数的倒数，并证明它与原数相乘得一。哪些输入是允许的？

目标定义是对 $x\ne0$ 有 $r(x)=1/x$。把限制写进函数本身：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
reciprocal(-4) = -1 / 4
```

输入括号里，`x R` 给出集合，`: x != 0` 给出额外输入条件。括号后的 `R` 是输出集合。Litex 对每个合法输入检查函数体 `1 / x`。

这是数学接口的重要部分。之后每次调用 `reciprocal` 都必须给出非零实数实参。限制属于定义，调用者不必到后面的证明里去找。

下面是**有意失败的定义**；不要把它留在成品文件里：

```text
have fn reciprocal(x R) R = 1 / x
```

它允许零，尽管函数体用 `x` 做除数。第一步修复是恢复非零输入条件。后面再长的性质证明，也不能让除以零变得有意义。

**试一试：** 在通过的块里，把最后一行改成 `reciprocal(0) = 0`。预期会在函数输入条件处失败。然后恢复合法输入。

**带走：** 定义域是数学的一部分。被拒绝的函数调用，可能在尝试证明之前就先是表达式意义的问题。

## 4. 从例子走到一般事实

在 `2` 和 `-4` 处检查值，并不能证明对每个非零实数都成立的规律。用量化写出主张的真正范围。

### 对每个输入

**问题：** 把实数加倍，是否与它加自己一致？

```litex
have fn double(x R) R = 2 * x

forall x R:
    double(x) = x + x
```

把 `forall x R:` 读作“对每个实数 `x`”。缩进体是要检查的事实。全称陈述里的绑定 `x` 是局部的；它不是带选定值的新全局数。

函数自己的参数与全称陈述的参数碰巧同名。它们的作用域是分开的。缩进告诉你哪个体属于哪个头。

### 若条件成立

**问题：** 若一个实数为正，能推出什么？

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

`=>:` 上面的事实是**假设**，下面是**结论**。这句话说：对每个实数 `x`，**若** `x > 0`，**则** `x != 0`。

假设局部于这个蕴含。它不断言每个实数都为正，也不让无关的全局 `x > 0` 可用。没有假设时，像加倍例子那样，把结论直接写在 `forall` 下面。

### 当你想展示路径

若验证器已有必要规则，普通全称事实可以直接通过。若你想提供证明步骤，就引入 `claim`。

**问题：** 我 8 岁。哥哥比我大 5 岁。妈妈的年龄是哥哥年龄的三倍减 2。妈妈几岁？

证明思路是先算哥哥年龄：$8+5=13$。再算妈妈年龄：$3\cdot13-2=37$。

```litex
claim:
    ? forall my_age, brother_age, mother_age Z:
        my_age = 8
        brother_age = my_age + 5
        mother_age = 3 * brother_age - 2
        =>:
            mother_age = 37
    brother_age = my_age + 5 = 13
    mother_age = 3 * brother_age - 2 = 37
```

`?` 标记这个证明块的**目标**。这里目标是整个条件全称陈述。在证明体中，其参数与假设可用，所以两行计算能用到它们。

最后一行相对这些假设与先前步骤被检查。目标不会仅仅因为写在 `?` 后面就被接受。`claim` 成功后，完成的目标在块外可用；局部参数名则不可用。

裸 `forall` 体里是事实。`by def`、`by cases` 这类证明命令属于 `claim` 等证明体。这样把“你在断言什么”与“你给出的建立路径”分开。

**试一试：** 把 `my_age = 8` 改成 `my_age = 9`。先在纸上算出两个新年龄，再一起更新中间值与目标。留下旧结论 `37` 不应通过。

**带走：** `forall` 陈述范围，`=>:` 陈述假设，`claim` 给你写推导的地方。

## 5. 写跟随数学本身的证明

好的第一份证明从数学动作开始。对倒数：代入定义方程，再消去非零因子。

### 定义、展开、计算

**问题：** 证明每当 $x$ 是非零实数时，$r(x)x=1$。

```litex
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1
```

有三块含义要一起保持：

1. 定义把 `reciprocal` 限制在非零实数输入。
2. 目标把乘法律限制在同样的输入上。
3. 证明先露出定义方程，再用等式链建立该律。

行 `reciprocal(x) = 1 / x` 在乘进去之前把有用方程写清楚。最后一步等式用到 `x != 0`。证明跟随熟悉的数学论证，而不是在战术名字列表里搜索。

### 证明命名性质

**问题：** 证明每个到零的距离都非负。

```litex
have fn distance_from_zero(x R) R = |x|

prop is_nonnegative(t R):
    t >= 0

claim:
    ? forall x R:
        $is_nonnegative(distance_from_zero(x))
    distance_from_zero(x) = |x| >= 0
    by def $is_nonnegative(distance_from_zero(x))
```

计算建立数值条件。`by def` 再检查该条件是否给出命名性质的含义。函数定义与性质定义职责不同：前者给出值，后者描述该值。

### 分情形证明

**问题：** 负输入置零，其余输入不变。这个操作是否总返回非负数？

对实数输入，要么 `x < 0`，要么 `x >= 0`。第一种情形输出是零；第二种是输入本身：

```litex
have fn clamp_at_zero(x R) R by cases:
    case x < 0: 0
    case x >= 0: x

claim:
    ? forall x R:
        clamp_at_zero(x) >= 0
    by cases:
        ? clamp_at_zero(x) >= 0
        case x < 0:
            clamp_at_zero(x) = 0
            0 >= 0
        case x >= 0:
            clamp_at_zero(x) = x
            x >= 0
```

定义在每个情形选一个值。证明在每个分支检查同一目标。分支必须覆盖可能性；挑两个方便的例子不能建立全称结果。

这些例子里，有些简单结论其实已被推断。我们仍保留定义方程与具体分支结论，因为它们说明数学动作。你不必把每个例行算术或隶属后果都扩成单独证明。

**试一试：** 在完整块末尾追加 `clamp_at_zero(-2) = 0` 与 `clamp_at_zero(2) = 2`。再试把负分支改成 `-1`。预测全称证明的哪一部分会失败。

**带走：** 写下你需要的数学步骤：展开定义、给出有用中间等式，或做穷尽分情形。每一步仍须在实际上下文中被检查。

## 6. 读懂失败并做小修复

失败的检查要求你查看源码与第一个失败阶段。它并不自动证明你的数学目标为假。

### 失败 A：表达式超出定义域

这个**有意失败块**定义了合法倒数，却在过大定义域上要求定律：

```text
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        reciprocal(x) * x = 1
    reciprocal(x) * x = 1
```

这里 `x` 是任意实数。没有排除零，所以目标含有输入条件缺失的函数应用。先修复目标，再谈扩展证明：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1
```

这恢复了我们一开始想要的陈述：非零实数输入上的乘积律。我们没有在零处证明定律，也没有改函数去接纳其方程无意义的输入。

### 失败 B：上下文建立不了该事实

这是另一个**有意失败块**：

```text
have x R
x != 0
```

表达式有意义，但任意实数不必非零。先想清楚你想要的数学。若 `x` 本意是具体值 `2`，就引入该值：

```litex
have x R = 2
x != 0
```

若你想要关于任意非零数的条件律，就把条件写成假设，如倒数证明那样。若目标本应从已有事实推出，就补上缺失的中间事实，或使用已建立结果。没有数学理由就加假设，等于改了问题。

### 在正确层级阅读结果

本地批量命令如 `litex -lang en -strict -f first.lit` 返回 JSON。先看整体 `run_result`，再检查 `statement_results` 中的拒绝项。`session_terminated` 和 `termination` 报告硬错误；普通验证失败时它们分别为 false 和 null。失败批处理以非零状态退出。成功批处理要求退出状态为零且 `run_result == "success"`。

下面是成功文件结果的**选字段摘录**；其他字段（含语句结果）已省略：

```json
{
  "kind": "run",
  "run_result": "success",
  "target": "file",
  "session_terminated": false, "termination": null
}
```

对失败 A，失败 `claim` 的反馈指出目标的良定义检查。“良定义”在这里指具体问题：`reciprocal(x)` 是否有合法输入。这与检查随后的消去证明不同。其失败 `statement_results` 条目的**选字段摘录**是：

```json
{
  "statement_result": "rejected",
  "why_failed": {
    "phase": "claim",
    "failure": {
      "phase": "goal_wd"
    }
  }
}
```

完整结果还包括源码，以及对未满足 `x != 0` 要求的嵌套失败。把实际语句与解释一起读；详细字段名可能随版本变化。机器使用请以 [JSON 约定](Litex命令行参考.md#json-output-contract) 为准。

| 你先看到的问题 | 先检查什么 |
| --- | --- |
| 解析或缩进 | 精确源码形状，以及哪个体被缩进 |
| 未知名字 | 其声明、拼写与作用域 |
| 非法实参或除法 | 隶属与定义域条件，尤其非零除数 |
| 目标仍未证明 | 可用假设、定义，以及下一步小推导 |
| 前面成功后面失败 | 成功语句到底使什么变为可用 |

Litex 对许多例行事实有内置检查与推断，但不是每个真陈述的完全自动求解器。失败可能暴露缺失证明步骤、尚不支持的自动化，或语言/库缺口。例如，你可以独立证明某个假等式为假；不能仅因 Litex 未能证明某命题，就推断其否定。

### 交互修复时保留已接受工作

本地书写时，在练习目录开启 `-session`，先接受一条声明：

```bash
litex -lang en -session -e 'have a R = 2'
```

向同一个进程一次提交一条顶层语句；缩进块以空行结束。下面这份已检查的会话记录缩略了失败 JSON：

```text
litex> a = 3
{"run_result": "failure", ..., "session_terminated": false, "termination": null}
litex> a + 1 = 3
success
```

`a = 3` 失败，但已接受的 `a = 2` 仍能支持下一句计算。对照独立进程：

```bash
litex -lang en -e 'have a R = 2'
litex -lang en -e 'a + 1 = 3'
```

第一条命令成功；第二条失败，因为它没有 `a` 的声明，需要重新加载已接受源码。对于已通过的保存文件，用 `litex -session -f first.lit` 启动一次，随后继续提交新语句。不要每做一个小改动就重启或从头重新运行整个文件。

普通失败回到提示符后，已接受的声明仍在。在同一会话里修复失败语句。复合 `claim` 是一条语句；粘贴的多条独立语句即使后面失败，前面成功仍可保留。

若进程停止，或你需要替换已在同名下接受的定义，就开新会话并重放已接受源码。从干净进程检查的已保存文件才是最终证据；仅凭交互结果可能依赖你忘了保存的先前输入。

### 知道成功检查假设了什么

本课程例子不使用用户 `trust` 或 `axiom` 语句。`-strict` 拒绝这些语句，包括证明内部或其依赖里的。它仍依赖 Litex 的实现、内置规则与允许的基础接口。它不是对检查器自身的独立证明。

你可能在其他材料里遇到 `trust`。它显式接受事实而不完成证明。用它把练习变绿，会留下证明义务；它并不教你如何证明该练习。需要此功能时读 [trust 边界](Litex手册.md#trust-and-strict-mode)。

**试一试：** 运行失败 A，找到失败的 `claim`，修复其定义域。再运行失败 B，解释为什么问题不同。最后在新进程中检查修复后的整文件。

**带走：** 诊断第一个失败义务，改最小相关部分，再检查完整已保存源码。

## 7. 完成你的第一份 lit 文件

你现在足以做出一份小的数学文件，让其他读者或 agent 可以复现。

**你的项目：** 在非零实数上定义倒数。证明其乘积律。检查一个具体用法。再定义到零的距离，并证明它非负。

先用自己的话写出数学计划：

- 倒数是 `1 / x`；输入必须是非零实数。
- 代入该方程并消去非零因子，证明乘积律。
- 到零的距离是绝对值，它非负。

把下面完整源码存为 `first.lit`。注释以 `#` 开头：

```litex
# Reciprocal of a nonzero real number.
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1

reciprocal(2) * 2 = 1
reciprocal(2) * 4 = (reciprocal(2) * 2) * 2 = 2

# Distance from zero and a property of its output.
have fn distance_from_zero(x R) R = |x|

prop is_nonnegative(t R):
    t >= 0

claim:
    ? forall x R:
        $is_nonnegative(distance_from_zero(x))
    distance_from_zero(x) = |x| >= 0
    by def $is_nonnegative(distance_from_zero(x))

distance_from_zero(-3) = 3
by def $is_nonnegative(distance_from_zero(-3))
```

检查已保存文件：

```bash
litex -lang en -strict -f first.lit
```

分享时把源码与结果放在一起。有用的结果应说明：你跑了哪个文件与检查器版本、整次运行是否成功、是否加入了任何假设或证明债务。它不应只展示较长失败文件中的一行成功。

### 是什么让它一眼可认作 Litex？

已检查文件暴露对象、其含义，以及后续语句可消费的事实。你可以把 `reciprocal(x) = 1 / x` 读成你在纸上会写的同一步。检查器处理支持的例行后果；需要时你提供定义域与有用推导。

这是面向事实的证明接口。在本文件中，意思是：第一个 `claim` 建立乘积律，后面的计算可以使用它。这并不表示每句数学都能无证明地检查，也不表示 Litex 与另一证明助手有相同覆盖面。

### 为什么这可以成为给 AI 的数学

AI 模型可以提出你刚写的定义、目标与证明步骤。Litex 提供检查这些提议的数学接口：显式输入条件、能留下可用上下文的陈述，以及可指向下一次修复的反馈。`.lit` 文件以后续 agent 可读可再跑的形式记录已接受发展。

重点是给 AI 一种构造与修订已检查数学知识的方式。倒数例子演示该接口；它并不建立“agent 总能解题”或“此工作流优于其他系统”。人类仍拥有意图中的定义、定义域、假设与最终数学陈述。

### 已检查文件之后还能做什么？

| 路线 | 用途 | 需保持可见的边界 |
| --- | --- | --- |
| Python 或 C 抽取 | 可执行数值片段 | 实验性支持子集；任意 `have fn` 不会自动变成可执行程序。源码证明不建立浮点精度。 |
| 图视图 | 查看语句及其证据之间的关系 | 依赖图谱工具及其暴露的证据；画出的边不是额外证明。 |
| LaTeX 渲染 | 阅读与呈现数学 | 渲染可从已解析源码工作；好看输出本身不表示源码已验证。 |
| Lean 输出 | 把支持的已检查推理重放到另一证明语言 | 预览子集；生成输出必须通过其自身的 Lean 检查，原生数学陈述可能需要适配器。 |

把验证与导出当作分开的步骤。在选择导出路线前，阅读当前 [CLI 参考](Litex命令行参考.md#commands)、[Lean 边界](Litex命令行参考.md#lean-compiler-boundary) 与 [LaTeX 指南](Litex命令行参考.md#latex-conversion-preview)。这些链接描述当前接口；本课程最终文件是已检查的数学产物，不是承诺每条路线都接受其全部语句。

### 检查你的理解

不看上面的解释，回答这些问题：

1. `have x R = 2` 比 `have x R` 多提供了什么信息？
2. 为什么倒数的签名包含 `x != 0`？
3. `prop` 声明与已证明实例有什么区别？
4. 在你的倒数 `claim` 里，哪些行是假设、目标与证明？
5. 为什么失败检查可能意味着并非“陈述为假”？
6. 为什么最终文件要从新进程再跑一遍？

然后把具体倒数输入从 `2` 改成 `5`，并检查合适的乘积。再加一个你自己的距离例子。若你能解释定义域并修复故意失败，你已完成核心课程。你不必背完整语法参考。

## 可选扩展

在核心课程之后再选做。它们增加复用与构造工具，但不改变“陈述并检查事实”的基本习惯。

### A. 命名并复用定理 — 15 分钟

你第一份文件里的匿名 `claim` 已足以建立事实。当你想要调用方可引用的稳定结果时，命名的 `thm` 有用。

```litex
have fn reciprocal(x R: x != 0) R = 1 / x

thm reciprocal_product:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1

by thm reciprocal_product(2) => reciprocal(2) * 2 = 1
reciprocal(2) * 4 = (reciprocal(2) * 2) * 2 = 2
```

定理声明检查其证明。选定的调用检查输入与假设，然后发布所指的原子结论。若要未选定调用并发布定理的全部结论，用 `release thm reciprocal_product(2)`。这里我们只选要用的那一条事实。给每个简单算术恒等式命名会增加仪式感；当数学角色或复用使名字有帮助时再命名。

**试一试：** 把定理调用改成合法输入 `5`，并调整后续计算。再试在零处调用：定理的假设仍然重要。把最终文件中倒数 `claim` 换成这个命名定理，并在消费其结论的计算前做一次选定调用。

说明你从名字得到了什么：一个具体可复用结果，以及一个显式引用点。与先前匿名 `claim` 比较——其已检查事实在同一文件后续语句中已经可用。名字改善接口；它不会让未检查陈述变真。

把你的第一份发展保存在一份完整文件里。当更大项目需要分文件与依赖时，遵循 [项目组织参考](Litex手册.md#project-organization)，并同时验证生产者与真实调用方。单独成功的证明本身，不足以证明每个导出接口在另一模块里可用。

### B. 通过给出见证证明存在性 — 10 分钟

**问题：** 是否存在平方为四的实数？

给出满足条件的见证：

```litex
witness exist w R st {w^2 = 4} from 2
obtain root from exist w R st {w^2 = 4}
root^2 = 4
```

`exist w R st {...}` 表示“存在实数 `w` 使得花括号中的事实成立。”`witness ... from 2` 提供 `2`，并在代入后检查条件。`obtain` 从已检查的存在事实抽出新名字 `root`；它不会猜测任意方程的根。

名字 `w` 局部于存在陈述。抽出的 `root` 属于外围作用域。已知其平方为四；这并不告诉你 `root` 必须是正根。

对依赖全称量化输入的见证，在活跃输入的作用域内构造它：

```litex
claim:
    ? forall x R:
        exist y R st {y = x + 1}
    witness exist y R st {y = x + 1} from x + 1
```

先读数学动作：给定实数 `x`，选 `x + 1`。`claim` 导出全称存在陈述，而不是全局的 `x` 或 `y`。

`exist!` 额外要求唯一性。平方为四的问题有 `2` 与 `-2`，所以一个见证不是唯一存在性的证明。真正唯一的规范是：

```litex
witness exist! w R st {w = 2} from 2
```

**试一试：** 用 `-2` 作为平方为四的见证。解释为何这可通过，而声称唯一的平方四根会失败。

### C. 用同一课程与 AI agent 协作 — 5 分钟

给 agent 一个数学问题、相关定义，以及当前已检查源码。先要求自然语言证明思路，再要代码。Litex 的直接数学陈述、明确的验证反馈和保留上下文的 Session，为 agent 提供了具体的交互循环。对本课程，有用的请求是：

```text
Define reciprocal on nonzero real inputs in Litex.
Prove reciprocal(x) * x = 1 under that input condition.
Explain the proof idea, then return a complete standalone .lit file.
Use no trust or axiom. Keep the domain and conclusion unchanged.
Write and repair statements in one live -session; retain accepted context
after ordinary failures. Do not rerun the whole file after each small edit.
Run the checker; if it fails, show the first failed obligation and the
smallest repair. Finish with a clean whole-file check and its result.
```

循环就是你已练习过的：提出陈述或证明步骤，检查，读反馈，修复，在同一个 `-session` 中保留已接受工作。普通交互失败会保留先前成功。保存源码，让新进程能复现完整结果。

[Litex Agent 协作流程图](https://litexlang.com/assets/diagrams/litex-agent-pipeline-v1.png) 展示了人、AI 与验证器之间的这一协作循环。

检查器不决定 agent 是否形式化了你真正想要的问题。在把成功运行当作原问题的答案之前，复查定义、定义域、假设与结论。更长的 agent 会话与重放纪律，见 [Agent Guide](Litex智能体指南.md)。

## 核心检查点答案

1. `have x R = 2` 增加了具体值等式；`have x R` 只引入任意实数对象及其隶属关系。
2. 倒数除以输入。零必须在定义中排除，使用它的定理也须满足同一条件。
3. `prop` 给出含义。已证明实例建立：在特定实参处定义条件成立。
4. 在倒数 `claim` 中，`x != 0` 是假设；`?` 后的陈述是整个目标；其下两条等式是证明体。
5. 失败可能涉及解析、名字、定义域、缺失证明步骤，或检查限制。它不建立命题的否定。
6. 新文件运行检查所需上下文是否都已保存，以及是否有忘记保存的交互输入在供给证明。

年龄练习若 `my_age = 9`，哥哥是 `14`，妈妈是 `40`。clamp 练习中，负分支返回 `-1` 无法证明非负输出律。在 `5` 处的倒数，合适事实是 `reciprocal(5) * 5 = 1`。

<a id="learn-math-with-litex"></a>

## Learn Math with Litex：数学例子

下面把八个数学问题直接写成可学习、可运行的例子。每个单元先解释数学思路，再给出完整 Litex 代码与练习。需要的定义就在该单元内；每块代码都应在新环境中独立运行，不要求先运行其他例子。

可以按表中的顺序学习，也可以单独选读。前三例使用算术与中学代数；极限与导数的例子会在这里介绍所需的误差定义。这些专题另计学习时间，不包含在前面主课程的 90 分钟估计中。

| 例子 | 数学重点 |
| --- | --- |
| [1. 偶数乘一个自然数，为什么还是偶数？](#learn-math-even) | 从定义构造证明 |
| [2. 除以 $x$ 之前，我们需要知道什么？](#learn-math-division) | 定义域与非零条件 |
| [3. 为什么 $2^n \ge n+1$？](#learn-math-induction) | 数学归纳法 |
| [4. 怎样证明两个集合相等？](#learn-math-sets) | 元素法、双向包含 |
| [5. “任意”和“存在”的顺序有什么影响？](#learn-math-quantifiers) | 量词与依赖关系 |
| [6. 数列收敛到底承诺了什么？](#learn-math-convergence) | epsilon 与尾部控制 |
| [7. 为什么一个数列不能有两个极限？](#learn-math-uniqueness) | 三角不等式、反证法 |
| [8. $x^2$ 的导数为什么是 $2x$？](#learn-math-derivative) | 差商与误差估计 |

<a id="learn-math-even"></a>

### 1. 偶数乘一个自然数，为什么还是偶数？

**问题：** 已知自然数 $n$ 是偶数，为什么对任意自然数 $m$，$mn$ 仍是偶数？

“偶数”的定义给出了一个见证：存在自然数 $k$ 使 $n=2k$。于是 $mn=m(2k)=2(mk)$，新的见证就是 $mk$。证明的关键是找出这个数，而不是只检查几个乘积。

```litex
prop even(n N):
    exist k N st {n = 2 * k}

thm even_mul:
    ? forall m, n N:
        $even(n)
        =>:
            $even(m * n)
    obtain k from $even(n)
    witness $even(m * n) from m * k:
        m * n = m * (2 * k) = 2 * (m * k)

witness $even(6) from 3
release thm even_mul(5, 6)
```

把 `prop even(n N)` 读作偶数的定义。`obtain k` 从已知偶数事实中取出一个见证；`witness ... from m * k` 提供乘积的见证。等式链说明它确实满足定义。

最后两行先用 $3$ 证明 $6$ 是偶数，再把定理用于 $5$ 和 $6$，得到 $30$ 是偶数。自然数集 `N` 包含零，结论也包括 $m=0$。

**试一试：** 用同一定义证明两个偶数的和仍是偶数。若 $a=2u$、$b=2v$，你应该提供什么见证？

[下一例：除以 $x$ 之前，我们需要知道什么？](#learn-math-division)

<a id="learn-math-division"></a>

### 2. 除以 $x$ 之前，我们需要知道什么？

**问题：** 对实数 $x$，为什么不能不加条件地写“倒数乘以原数等于一”？

倒数 $1/x$ 的定义域是非零实数。先把 $x\ne0$ 写进函数输入条件，再证明 $(1/x)x=1$；证明中的假设与函数的合法输入相同。

```litex
have fn reciprocal(x R: x != 0) R = 1 / x

claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) * x = (1 / x) * x = 1

reciprocal(2) = 1 / 2
reciprocal(-4) = -1 / 4
```

非零条件出现在两个不同的位置：函数定义限制哪些输入可以调用它；全称证明说明结论对哪些实数成立。证明体把函数值展开成 $1/x$，再计算乘积。

下面是**完整的预期失败例子**，用 `text` 标出，不属于应当通过的代码块：

```text
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(0) = 0
```

失败发生在 `reciprocal(0)` 的输入条件检查处，零不满足 `x != 0`。检查器还没有一个合法的倒数表达式可用于后面的等式证明。

**试一试：** 在通过的代码中检查 `reciprocal(5) * 5 = 1`。再解释为什么把函数的非零条件删除，会使定义本身出问题。

[下一例：为什么 $2^n \ge n+1$？](#learn-math-induction)

<a id="learn-math-induction"></a>

### 3. 为什么 $2^n \ge n+1$？

**问题：** 如何证明每个自然数 $n$ 都满足 $2^n\ge n+1$？

基础步 $n=0$ 是 $1\ge1$。归纳步假设 $2^n\ge n+1$，则 $2^{n+1}=2\cdot2^n\ge2(n+1)=(n+2)+n\ge n+2$，最后一步使用 $n\ge0$。

```litex
thm power_two_lower_bound:
    ? forall n N:
        2^n >= n + 1
    by induc n from 0:
        ? 2^n >= n + 1
        ? from n = 0:
            2^0 = 1 = 0 + 1
        ? induc:
            2^(n + 1) = 2^n * 2^1 = 2^n * 2 >= (n + 1) * 2 = (n + 1 + 1) + n >= n + 1 + 1

release thm power_two_lower_bound(4)
```

`by induc n from 0` 从零开始归纳。`? from n = 0` 是基础步；`? induc` 是归纳步，其中当前的归纳假设可用。一条等式与不等式链把乘方规律、归纳假设和 $n\ge0$ 接起来。

定理陈述覆盖所有自然数，最后的调用把它用于 $n=4$。这与只验证 $2^4\ge5$ 的具体计算不同。

**试一试：** 写出 $n=1,2,3$ 的数值检查，再说明为什么有限个检查不能替代归纳步。

[下一例：怎样证明两个集合相等？](#learn-math-sets)

<a id="learn-math-sets"></a>

### 4. 怎样证明两个集合相等？

**问题：** 为什么交换两个集合的顺序不改变交集，即 $S\cap T=T\cap S$？

集合相等意味着它们具有相同的元素。若 $x\in S\cap T$，则 $x\in S$ 且 $x\in T$，所以 $x\in T\cap S$。交换 $S,T$ 得到反向包含，两个包含关系给出相等。

```litex
claim:
    ? forall S, T set:
        intersect(S, T) = intersect(T, S)
    claim:
        ? forall x intersect(S, T):
            x $in intersect(T, S)
        x $in S
        x $in T
        x $in intersect(T, S)
    by def intersect(S, T) $subset intersect(T, S)
    claim:
        ? forall x intersect(T, S):
            x $in intersect(S, T)
        x $in T
        x $in S
        x $in intersect(S, T)
    by def intersect(T, S) $subset intersect(S, T)
    by extension intersect(S, T) = intersect(T, S)
```

两个内部 `claim` 各追踪一个元素，分别建立包含关系。`by def` 把“每个元素都属于另一集合”的全称事实折叠成 `$subset`。`by extension` 使用这两个包含关系证明集合相等。

这里的成员事实刻意保留，让读者看见元素怎样从一个交集进入另一个交集。Litex 对这类简单集合事实也有内置检查支持，例子展示的是数学证明的组织方式。

**试一试：** 在纸上把“属于交集”换成“属于并集”，解释为什么并集的证明需要处理两种可能，而不能同时断言元素属于两个集合。

[下一例：“任意”和“存在”的顺序有什么影响？](#learn-math-quantifiers)

<a id="learn-math-quantifiers"></a>

### 5. “任意”和“存在”的顺序有什么影响？

**问题：** “对每个实数 $x$，都存在 $y=x+1$”与“存在一个实数 $y$，对每个 $x$ 都有 $y=x+1$”是否相同？

第一句话允许看见 $x$ 后再选 $y$，所以选 $x+1$ 就行。第二句话要求一个固定的 $y$ 同时适用于所有 $x$：取 $x=0$ 得 $y=1$，取 $x=1$ 又得 $y=2$，不可能同时成立。

```litex
claim:
    ? forall x R:
        exist y R st {y = x + 1}
    witness exist y R st {y = x + 1} from x + 1
```

目标先绑定 `x`，证明体随后用 `x + 1` 构造 `y` 的见证。这正是“见证可以依赖前面的输入”。目标证明后导出整个全称存在陈述，局部名字 `x,y` 不成为全局对象。

把两句话写成数学公式，顺序差别就很清楚：

$$
\forall x\in\mathbb R\;\exists y\in\mathbb R:\ y=x+1,
\qquad
\exists y\in\mathbb R\;\forall x\in\mathbb R:\ y=x+1.
$$

**试一试：** 把等式改成 $y=2x$，分别判断两个量词顺序对应的命题。再考虑 $y=0$，这时固定见证能否适用于所有 $x$？

[下一例：数列收敛到底承诺了什么？](#learn-math-convergence)

<a id="learn-math-convergence"></a>

### 6. 数列收敛到底承诺了什么？

**问题：** “数列 $a_n$ 趋近于 $L$”的精确含义是什么？为什么常数列 $a_n=3$ 收敛于 $3$？

给定任意误差 $\epsilon>0$，必须找到一个起始下标 $n_0$，使每个 $n\ge n_0$ 都满足 $|a_n-L|<\epsilon$。常数列的误差恒为零，所以对任意正误差都可以选 $n_0=1$。这里的数列从正自然数 $1$ 开始索引。

```litex
prop is_tail_close_to(a fn(index N+) R, L R, epsilon R+, n0 N+):
    forall n N+:
        n >= n0
        =>:
            |a(n) - L| < epsilon

prop has_eventual_closeness_to(a fn(index N+) R, L R, epsilon R+):
    exist n0 N+ st {$is_tail_close_to(a, L, epsilon, n0)}

prop has_limit(a fn(index N+) R, L R):
    forall epsilon R+:
        $has_eventual_closeness_to(a, L, epsilon)

have fn constant_sequence(n N+) R = 3

claim:
    ? $has_limit(constant_sequence, 3)
    claim:
        ? forall epsilon R+:
            $has_eventual_closeness_to(constant_sequence, 3, epsilon)
        claim:
            ? forall n N+:
                n >= 1
                =>:
                    |constant_sequence(n) - 3| < epsilon
            |constant_sequence(n) - 3| = |3 - 3| = 0 < epsilon
        by def $is_tail_close_to(constant_sequence, 3, epsilon, 1)
        witness $has_eventual_closeness_to(constant_sequence, 3, epsilon) from 1
    by def $has_limit(constant_sequence, 3)
```

三层定义分别说明“这个尾部够近”“存在够近的尾部”“每个正误差都有够近的尾部”。`has_limit(a, L)` 陈述 $L$ 是 $a$ 的极限，尚未定义一个返回极限值的函数。

证明先处理任意 `epsilon`，验证从 $1$ 开始的整个尾部，再用 $1$ 作起始下标的见证。三个定义都在同一块中，运行不依赖前面的例子。

**试一试：** 把常数值与极限候选从 $3$ 一起改成 $5$，证明怎样变化？再解释为什么只改变前者而保留候选 $3$ 不会得到同样的证明。

[下一例：为什么一个数列不能有两个极限？](#learn-math-uniqueness)

<a id="learn-math-uniqueness"></a>

### 7. 为什么一个数列不能有两个极限？

**问题：** 如果同一个数列收敛于 $L_1$ 与 $L_2$，为什么这两个数必须相等？

假设它们不同，令距离 $D=|L_1-L_2|>0$，取 $\epsilon=D/3$。两个收敛条件各给出一个尾部。选同时位于两个尾部的下标，三角不等式就给出 $D<2\epsilon=2D/3<D$，矛盾。

下面重新列出完整极限定义，使这个例子也能单独运行。

```litex
prop is_tail_close_to(a fn(index N+) R, L R, epsilon R+, n0 N+):
    forall n N+:
        n >= n0
        =>:
            |a(n) - L| < epsilon

prop has_eventual_closeness_to(a fn(index N+) R, L R, epsilon R+):
    exist n0 N+ st {$is_tail_close_to(a, L, epsilon, n0)}

prop has_limit(a fn(index N+) R, L R):
    forall epsilon R+:
        $has_eventual_closeness_to(a, L, epsilon)

thm sequence_limit_unique:
    ? forall a fn(index N+) R, L1, L2 R:
        $has_limit(a, L1)
        $has_limit(a, L2)
        =>:
            L1 = L2
    by contra:
        ? L1 = L2
        L1 - L2 != 0
        0 < |L1 - L2|
        have epsilon R+ = |L1 - L2| / 3
        obtain n1 from $has_eventual_closeness_to(a, L1, epsilon)
        obtain n2 from $has_eventual_closeness_to(a, L2, epsilon)
        have n0 N+ = n1 + n2
        n0 >= n1
        n0 >= n2
        |a(n0) - L1| < epsilon
        |a(n0) - L2| < epsilon
        |L1 - a(n0)| = |a(n0) - L1|
        |L1 - L2| <= |L1 - a(n0)| + |a(n0) - L2| < epsilon + epsilon
        epsilon + epsilon = |L1 - L2| / 3 + |L1 - L2| / 3 = (2 / 3) * |L1 - L2| < 1 * |L1 - L2| = |L1 - L2|
        |L1 - L2| <= |L1 - a(n0)| + |a(n0) - L2| < |L1 - L2|
        impossible |L1 - L2| = |L1 - L2|
```

`by contra` 在“两个极限不同”的假设下寻找矛盾。两个 `obtain` 分别取出尾部起始下标；因为它们是正自然数，$n_1+n_2$ 至少与两者一样大，因此同一个数列项同时满足两份误差约束。

最后的计算把三角不等式与 $2D/3<D$ 接起来，再明确写出 $D\le\text{两段距离之和}<D$。在这个矛盾上下文中，`impossible` 用恒等事实 $D=D$ 收束反证。这里证明了极限的唯一性，并没有证明每个数列都有极限。

**试一试：** 先在纸上将 $\epsilon$ 改成 $D/4$，看看最后的估计怎样变化。如果只选 $n_1$，为什么不能保证第二份尾部约束也适用？

[下一例：$x^2$ 的导数为什么是 $2x$？](#learn-math-derivative)

<a id="learn-math-derivative"></a>

### 8. $x^2$ 的导数为什么是 $2x$？

**问题：** 在点 $x_0$，怎样从差商定义得到平方函数的导数 $2x_0$？

连接 $(x_0,x_0^2)$ 与 $(x,x^2)$ 的割线斜率是
$$
\frac{x^2-x_0^2}{x-x_0}=x+x_0\qquad(x\ne x_0).
$$
它与候选切线斜率 $2x_0$ 的差恰好是 $x-x_0$。因此要把斜率误差限制在 $\epsilon$ 内，只需令 $0<|x-x_0|<\delta$ 并选择 $\delta=\epsilon$。

先在 $x_0=3$ 附近看几个值。写 $x=3+h$，差商是 $6+h$：

| $h$ | 割线斜率 | 与 $6$ 的距离 |
| --- | --- | --- |
| $-0.1$ | $5.9$ | $0.1$ |
| $-0.01$ | $5.99$ | $0.01$ |
| $0.01$ | $6.01$ | $0.01$ |
| $0.1$ | $6.1$ | $0.1$ |

这些数值帮助建立直觉；下面的证明说明为什么任意足够小的非零 $h$ 都满足误差要求。

```litex
prop derivative_delta_controlled(f fn(u R) R, x0, L R, epsilon, delta R+):
    forall x R:
        x != x0
        |x - x0| < delta
        =>:
            |(f(x) - f(x0)) / (x - x0) - L| < epsilon

prop has_derivative_at_R(f fn(u R) R, x0, L R):
    forall epsilon R+:
        exist delta R+ st {$derivative_delta_controlled(f, x0, L, epsilon, delta)}

have fn square_function(x R) R = x^2

thm square_difference_quotient:
    ? forall x0, x R:
        x != x0
        =>:
            (square_function(x) - square_function(x0)) / (x - x0) = x + x0
    x - x0 != 0
    square_function(x) - square_function(x0) = x^2 - x0^2 = (x - x0) * (x + x0)
    (square_function(x) - square_function(x0)) / (x - x0) = ((x - x0) * (x + x0)) / (x - x0) = x + x0

thm square_function_has_derivative_at:
    ? forall x0 R:
        $has_derivative_at_R(square_function, x0, 2 * x0)
    claim:
        ? forall epsilon R+:
            exist delta R+ st {$derivative_delta_controlled(square_function, x0, 2 * x0, epsilon, delta)}
        witness exist delta R+ st {$derivative_delta_controlled(square_function, x0, 2 * x0, epsilon, delta)} from epsilon:
            claim:
                ? forall x R:
                    x != x0
                    |x - x0| < epsilon
                    =>:
                        |(square_function(x) - square_function(x0)) / (x - x0) - 2 * x0| < epsilon
                release thm square_difference_quotient(x0, x)
                (square_function(x) - square_function(x0)) / (x - x0) - 2 * x0 = (x + x0) - 2 * x0 = x - x0
                |(square_function(x) - square_function(x0)) / (x - x0) - 2 * x0| = |x - x0| < epsilon
            by def $derivative_delta_controlled(square_function, x0, 2 * x0, epsilon, epsilon)
    by def $has_derivative_at_R(square_function, x0, 2 * x0)

release thm square_function_has_derivative_at(3)

forall x R:
    square_function(x) - (9 + 6 * (x - 3)) = (x - 3)^2
```

第一个定义把差商的合法条件 `x != x0` 与误差界放在一起。第二个定义要求：每个正误差都有一个正的邻域半径。`has_derivative_at_R(f, x0, L)` 是关于所给候选值 $L$ 的导数关系，例子没有假定一个适用于所有函数的导数算子。

`square_difference_quotient` 用平方差因式分解证明差商公式。随后为任意 `epsilon` 选择 `delta = epsilon`；误差等式直接把导数条件化为已知的 `|x - x0| < epsilon`。

在 $3$ 处调用定理得到候选斜率 $6$。最后的恒等式给出切线 $y=9+6(x-3)$ 与抛物线的精确差 $(x-3)^2$，这也解释了切线为何在该点附近贴近曲线。

**试一试：** 把定理调用的点改成 $2$，预期斜率是多少？写出对应的切线与平方误差。再解释为什么把 $x=x_0$ 直接代入差商不能完成导数证明。

[返回数学例子目录](#learn-math-with-litex)

## 从你接下来想做的事继续

| 你的下一任务 | 接着读 |
| --- | --- |
| 继续练习具体数学问题 | [Learn Math with Litex：数学例子](#learn-math-with-litex) |
| 找合适的声明或证明动作 | [Learner Cheatsheet](Litex学习速查表.md) |
| 查阅精确语法、语义或证明模式 | [Manual](Litex手册.md) |
| 安装 Litex 或理解 CLI 反馈 | [Setup](安装Litex.md) 与 [CLI](Litex命令行参考.md) |
| 理解语言的研究方向 | [Litex 蓝图](Litex中文蓝图.md) |
| 搭建可复现的 agent 工作流 | [Agent Guide](Litex智能体指南.md) |

对你的下一份文件，选一个你能在纸上解出的小问题。先写对象与合法输入，精确陈述要证明什么，再一步步按有用的数学动作增长已检查源码。

本指南中的 28 个独立 Litex 例子于 2026-10-12，用 Litex 1.0.6-beta 的当前源码发布构建、英文输出与严格模式检查通过。预期失败另有标注。Litex 仍在演进；若例子行为不同，请把完整源码与检查器版本连同反馈一起保留。
