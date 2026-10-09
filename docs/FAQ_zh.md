<a id="litex-faq"></a>

# Litex 常见问题

由沈嘉辰创建和维护。

Markdown 源码：https://github.com/litexlang/golitex/blob/main/docs/FAQ.md

> **Litex 是一个仍处于 beta 阶段的实验性业余项目，使用中可能遇到不完善之处。**

本页汇集 Litex 设计、性能模型和预期证明风格的常见问题。这是一份持续更新的说明：回答应具体、克制，并贴近当前验证器行为。

<a id="does-everything-in-the-public-repository-count-as-finished"></a>

## 公开仓库中的所有内容都算完成了吗？

不算。Litex 公开开发，草稿、实验与不完整翻译仍可见，也可复用。只有当前测试、注明日期的状态、显式 `trust` 边界与已知限制支持完成的说法时，才把功能或证明视为完成。

不同自然语言下 Litex 源码相同。批量 Normal JSON 携带 `-lang` 选择的语言（默认 `en`）；中文输出本地化字段名与证明解释，包括 `"语言": "zh"`。见 [`docs/cli.md`](cli_zh.md)。

<a id="why-recommend-one-spelling-when-another-is-supported"></a>

## 既然另一种拼写也支持，为什么推荐一种拼写？

支持说明语言契约，推荐帮助读者书写一致源码。新代码优先使用 `release thm name(args)`，而非仍支持的裸 `by thm` 别名；使用缩进 `forall`，而非行内全称陈述；使用 `forall`、`R`、`$in` 等英文/ASCII 源码，而非文档列明的 Unicode 别名。其他形式仍被接受。缩进暴露前提/结论边界；规范拼写匹配诊断输出，便于输入与搜索。

`by thm name(args) => fact` 有独立用途：选择一条原子推论。需要这种上下文效果时应保留它。[学习指南](Litex_Learner_Cheatsheet_zh.md#supported-syntax-and-recommended-writing)展示支持与推荐形式；[常见卡点](Litex_Learner_Cheatsheet_zh.md#common-places-to-get-stuck)用小例子解释事实列表与证明命令、定义与实例、定义域、作用域和见证。

<a id="how-does-equality-reuse-known-equal-objects"></a>

## 相等证明如何复用已知的相等对象？

存储的 forall 等式通过两端的嵌套对象构造器、函数位置与参数洞检索。固定参数如 `f(0)` 若已有与 `g(0)` 的等式，匹配可使用完整值路径，不要求 `f=g`。固定子树先使用 Direct 身份/相等/计算，再进行受支持的构造器递降，其叶节点只使用 Direct。参数载体和定理前提仍需证明；查找键不是证明证据。见[已检查示例](../examples/proof_nodes/equal/by_known_forall/rigid_application_alias.lit)。

良定义性通过后，相等先检查精确 IR 或结构 alpha 身份与已存储相等路径，再读有限的已知元组性质，最后尝试允许的数学内置规则。存储路径保留产生它们的 FactId，并优先于可能引入新证明义务的规则，包括策略搜索内部。后续相等类搜索回退可用身份、允许的内置规则或构造器匹配比较两端类成员，记录左路径、新证明与右路径。这也让已知成员关系跨越 alpha 等价的命名函数集合。具有结构 alpha 相同端点的已存储等式，也可在新同伴桥接前引用。重命名求和绑定变量保持可复用；改变自由函数、函数体、界或载体则不保持。这个只读检查不改写相等键。同伴证明不能递归扩展更多相等类，也不能启用已禁用的内置入口。更大的类仍意味着更多候选比较。[相等 README](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/README.md)展示完整调用与结果结构。

例如，`have p cart(R,R)` 现在让 `p = (p(1),p(2))` 引用笛卡尔积成员关系。`have p cart(R,R) = (a,b)` 时，`p(1) = a` 引用存储等式。返回元组的函数也可在应用 WD 和一次检查过的函数体代换后投影。已知形状提供元组与索引要求，无需用户另写成员关系桥接。此路线保留来源 FactId，不递归展开嵌套函数体，也不接受越界索引。见[函数示例](../examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit)。模板函数别名通过存储相等路径保留已检查签名。命名应用结果能提供元组值或坐标，无需先断言完整元组等式；见[模板别名示例](../examples/stmt_nodes/definition/template_alias_struct_tuple.lit)。

声明为返回集合的模板函数可以展开，而不把函数体视为新函数声明。父应用已检查模板参数、输入载体和保护条件；定义规则匹配完整定义域，以现有受限权限验证代换后的残余目标。这是经过检查的定义使用，不是假设集合身份，也不是一般递归求值器。见[集合值模板示例](../examples/proof_nodes/equal/by_object_definition/by_template/set_valued_application.lit)。

`y = x + 1 = 3` 等显式链检查相邻步骤，也存储端点 `y = 3`，后续可复用。对于 `have x R = 2` 和 `have y R = x + 1`，用此链暴露定义与计算；定义展开保持残余改写禁用。见[可运行示例](../examples/proof_nodes/chain/named_definition_endpoint.lit)。

<a id="can-definition-time-properties-be-used-with-builtin-entry-disabled"></a>

## 内置入口禁用时，还能使用定义时的性质吗？

能。原子目标通过良定义性后，共享 `by_known` 入口首先只用身份/存储路径参数匹配读取存储原子事实。失败后才开启既有的参数变换搜索，再进入 `known_special_property`。

对于良定义的应用，后者可匹配函数已记录签名，建立陪域或 `fn_range` 成员关系。它只读一般 Membership/Equality 事实索引，代入参数，引用身份或存储等式，不生成证明子目标，也不消耗内置入口或策略深度。无效应用仍在 WD 失败。

固定内置前提也使用此入口的只读形式，结果保留存储事实或定义性质证据。候选枚举和显式 FactId/历史检索保留各自接口。见[验证流水线](../src/execute/execute_fact_stmt/README.md)。

<a id="why-is-litex-called-litex"></a>

## 为什么叫 Litex？

Litex = Lisp + LaTeX。

Lisp 的启发不只在“数据即代码”，还在小而统一的核心、符号操作、树形程序、交互反馈，以及通过可组合小形式构建语言的风格。

LaTeX 的启发来自其书写数学的实用设计。

<a id="does-litex-support-multiple-output-languages"></a>

## Litex 支持多种输出语言吗？

Litex 源语言是共享的。批量 Normal JSON 默认使用英文键。`-lang zh` 将封装与语句键改为中文，并翻译规则名称与解释。源码语法不变；见 [`docs/cli.md`](cli_zh.md)。

<a id="how-is-litex-invented"></a>

## Litex 是怎样发明的？

通过不断实现和改进 Litex 语言。设计与实现并行发生。作者经历了 6000 次 Git 提交（大部分发生在 AI 尚未足够实用、不能帮他做内核开发的时候），才终于清楚自己在实现和设计什么。很难想象更好的方式。所有东西汇合起来时，会是一件美丽的事。

<a id="is-litex-a-programming-language"></a>

## Litex 是编程语言吗？

不是。Litex 是只为数学推理服务的领域语言，不是编程语言。舍弃编程语言功能，让它专注数学推理功能。这与 Lean、Coq 和 Isabelle 很不同，也让它能尽可能接近普通数学。

<a id="where-does-features-of-litex-come-from"></a>

## Litex 的功能来自哪里？

来自作者书写数学的经验。作者长期写数学，对数学推理过程有所理解；也长期写代码，对代码推理过程有所理解。他认为形式化语言应该像数学一样，为每个人所用。

多数功能来自数学与代码书写经验。核心验证过程 `match and substitute`（匹配与代换）模仿人如何验证事实：看到未证明事实时，尝试与已知事实匹配，成功后把已知事实的参数代入待证事实；若代换合法，该事实即得到证明。

Litex 的 `template` 受 C++ 的 `template`（数学对象可在不同集合上定义）和 Go 的 `interface`（模板参数必须满足性质）启发。

`struct` 受 C 的 `struct` 启发。

`claim`、`thm` 受数学书中 theorem 的含义启发。

`strategy` 和内置规则受人检查递归定义对象良定义性的方式启发。

`forall xxx set` 中 `xxx set` 表示 `$is_set(xxx)` 的语法糖，来自观察：谈论集合时，几乎总是在说“某物是集合”。因此 `set` 不独立出现在语言中，总与“某对象是集合”一同出现。

`fn(x R) R {(-x)}` 这样的匿名函数语法很重要，因为它们用作 `sum`、`product` 和 `\integral` 等函数的参数；它受 JavaScript `(x) => (-x)` 启发。

`tuple`、`cart` 和 `struct` 的联系很重要，因为包括 `struct` 在内的任何内容都必须对应集合论中的某物。Litex 中不应有任意、缺少具体数学意义的东西。参数固定后，`&Point` 就是某个笛卡尔载体的命名子集。`have p &Point = (0, 0)` 因而赋予 `p` 相应字段名，包括代表第一坐标的 `p.x`。

<a id="what-does-litex-is-built-on-relationships-between-objects-instead-of-meanings-of-them-mean"></a>

## “Litex 基于对象间关系，而不是对象的含义”是什么意思？

有理数 `Q` 可以构造为整数对的等价类，实数 `R` 有多种构造方式。Litex 不把某一种构造定为它们的内置定义。同样，`f fn(x R, y R) R` 可以建模为 `cart(R, R, R)` 中的图，也可以是 `cart(cart(R, R), R)` 中的图。Litex 直接暴露函数接口，不强制每位用户选用某种图编码。需要时，数学发展可以形式化特定构造，或用 `trust` 标记假设的兼容结果。内置接口关注可用关系，例如 `Z` 包含于 `Q`，以及函数应用的定义域和陪域行为。

中学欧几里得几何课上，老师会说所谓点、线、面、圆，并不是纸上画出的真实东西，而是具有特定性质的想象构造。本质上它们是什么并不重要，重要的是有公理规定它们之间的关系。虽然可以用更抽象概念（例如笛卡尔坐标）定义它们，但当只关注平行、相交等性质，且公理已能处理这些关系时，就无需考虑那种构造。实数、有理数等也可用更抽象概念定义，用户可以自行用 Litex 构造。更重要的是对象之间的关系，这正是 Litex 强调的。

阅读陶哲轩《Analysis One》中的内容：

```

Remark 2.1.14. Note that our definition of the natural numbers is ax- iomatic rather than constructive. We have not told you what the natural numbers are (so we do not address such questions as what the numbers are made of, are they physical objects, what do they measure, etc.) - we have only listed some things you can do with them (in fact, the only operation we have defined on them right now is the increment one) and some of the properties that they have. This is how mathematics works - it treats its objects abstractly, caring only about what properties the objects have, not what the objects are or what they mean. If one wants to do mathematics, it does not matter whether a natural number means a certain arrangement of beads on an abacus, or a certain organization of bits in a computer’s memory, or some more abstract concept with no physical substance; as long as you can increment them, see if two of them are equal, and later on do other arithmetic operations such as add and multiply, they qualify as numbers for mathematical purposes (provided they obey the requisite axioms, of course). It is possible to construct the natural numbers from other mathematical objects - from sets, for instance - but there are multiple ways to construct a working model of the natural numbers, and it is pointless, at least from a mathematician’s standpoint, as to argue about which model is the “true” one - as long as it obeys all the axioms and does all the right things, that’s good enough to do maths.

```

对 Litex 来说，它包含且只包含标准的数学性质。

<a id="why-does-litex-have-this-particular-menu-of-objects-and-statements"></a>

## 为什么 Litex 恰好选择这些对象与语句形式？

Litex 语法有意保持有限，并有明确设计取向。目标不是把所有证明引擎概念都变成新表层形式，而是保留少量能舒适书写普通数学、同时可检查的对象与语句形式。

某形式成为一等形式主要有两个原因。

第一，一些形式是基本数学或逻辑设施。相等、成员关系、数字字面量、算术、函数应用、`forall`、`exist`、合取、情况、见证、定义与证明块，是验证器必须直接理解的可信背景、逻辑组织或计算内容。若它们只能经由遥远抽象编码，几乎每份证明都会在抵达数学思路前把精力耗在记录维护上。

第二，一些形式是用户接口选择。数学家本就书写它们，通常还有近似的 LaTeX 写法：显式集合、元组、笛卡尔积、区间、求和、匿名函数、等式或不等式链、`have`、`claim`、`witness`、`by cases` 等证明动作。它们并非全都在基础意义上原始；存在是为了熟悉感，缩短纸面证明与已检查脚本的距离。

因此 `obj` 与 `statement` 是设计边界。对象是事实所谈论的数学表达式；语句是引入对象、定义词汇、断言事实与组织证明的动作。新对象或语句形式必须有充分理由：检查器需要它作为直接数学背景，或它能显著清晰化用户数学表层。

这是 Litex 较独特的选择：以尽可能少的一等形式优化使用舒适度和数学熟悉感，而不是从最大一般性的编程语言或证明项演算开始。

<a id="why-can-an-or-branch-contain-an-and-if-and-contains-only-atomic-facts"></a>

## `and` 只有原子事实，为什么 `or` 分支能包含 `and`？

因为事实采用固定优先级层次。`and` 有意保持平坦，只包含原子事实。解析器先完成一个原子、关系链或平坦 `and` 分支，再由外围 `or` 收集它们。因此内部 `AndFact` 存原子事实，`OrFact` 存 `AndChainAtomicFact` 分支。这些固定形状也方便把已知 `or` 与目标 `or` 匹配。

例如 Litex 将：

```text
$p(a) and $q(a) or $t(a)
```

读作两个 `or` 分支 `($p(a) and $q(a))` 与 `$t(a)`。“`or` 是较高语法/AST 层”与“`and` 的绑定优先级更紧”，是从两个视角描述同一解析。这不使事实语法可任意递归嵌套：`and` 仍只有原子事实，`or` 只收集完整原子、链或平坦合取分支。

同样四种形状构成自动内置规则的有界前提语言。规则可以消费已知完整 `or`，而不声称某个分支单独已知。例如 `a = 1 or a = 2 or a = 3` 能证明 `a $in {1, 2, 3}`。验证器引入 `or` 时则必须证明一个选定分支。两个方向的每个原子叶都保留外围内置权限和深搜索预算；复合事实不会重开完整搜索。

全称结论也遵循有界语法。`forall` 结论不能包含另一 `forall`；应把量化参数全部绑定在外围头部，如 `forall x R, y R: ...`，而非在 `forall x R` 结论内放 `forall y R`。全称事实仍可在 `=>:` 前作为显式前提，因为前提存为假设事实，而不是结论分支。直接的 `not forall` 结论也会被拒绝；须先为量化命题命名。

因此有些普通逻辑形状没有直接匿名 Litex 语法。特别是，`forall` 不能直接作 `or` 分支，虽然 Lean 可以递归组合这种命题。闭合子命题可用零参数 `prop` 命名，再在外围使用原子调用：

当前解析器要求 `prop` 参数列表非空。以下闭合零参数谓词作为预期接口保留，不是可用语法。当前代码应使用有真实数学参数的谓词。

```litex
prop all_reals_reflexive():
    forall x R:
        x = x

by def $all_reals_reflexive()
$all_reals_reflexive() or 1 = 1 and 2 = 2
```

定义使 `$all_reals_reflexive()` 与定义体等价，不自动使定义体为真。若子命题有自由对象，给 `prop` 相应参数。命名既保留规范事实表示，也通过原子接口暴露目标数学陈述。

<a id="how-does-litex-parse-a-minus-sign-next-to-a-power"></a>

## 幂旁边的减号怎样解析？

幂比前缀负号绑定更紧，前缀负号又比乘、除、二元加减更紧。因此 `-t^2` 解析为 `-(t^2)`，`-t * u` 分组为 `(-t) * u`。幂仍右结合，`a^b^c` 表示 `a^(b^c)`。

书写时仍应显式说明负号/幂边界。平方的相反数写 `-(t^2)` 或 `-1 * (t^2)`；负值平方写 `(-t)^2`；负指数写 `t^(-1)`。这样人和书写代理能看见语法树，无需记忆或猜测解析规则。

<a id="what-are-builtin-objects-and-builtin-rules"></a>

## 什么是内置对象与内置规则？

理解 Litex 可从四个相关层次开始：

- `object` 是数学表达式，如 `x`、`x + 1`、`R`、`{1, 2}`、`|x|` 或 `fn(n N+) R`；
- `fact` 是对象的命题，如 `x > y`、`x $in R`、`1 + 2 = 3` 或 `x = y or x < y or x > y`；
- `statement` 是作用于数学上下文的行或块，如 `have`、`forall`、`claim`、`thm`、`witness`、`by cases` 或 `trust`；
- 验证规则是检查器判断事实是否从当前上下文成立的路线。

对象、事实形式与验证路线有内置支持。普通源码事实不会注入每次运行：包事实只有显式导入后才可用，并保留包命名空间。

**内置对象**是 Litex 直接理解的对象形式或名称。并非每个内置词都是对象：`not`、`and`、`or`、`forall`、`exist` 是表达事实和证明形状的逻辑或事实形式。内置对象头包括标准集合、算术操作、元组与集合形式或 `|x|`。有些主要为方便用户，例如绝对值 `|x|`：用户可自行从基本序与算术定义类似函数，但普通数学频繁使用它，因此内置标准拼写。

```litex
have fn self_abs(x R) R by cases:
    case x = 0: 0
    case x < 0: (-x)
    case x > 0: x
```

重点不是没有内置名称就不能表达 `abs`，而是写 `|x|` 能让验证器连接常用绝对值规则，无需每个文件重建接口。

**源码背景事实**是普通 Litex 事实，通常放在显式导入的项目或源码局部引用包中。**内置规则**则位于验证器内部。例如直接识别通常的实数三歧性：

```litex
forall x, y R:
    x = y or x < y or x > y
```

内置规则也能产生普通对象定义所用的基本实数比较见证：

```litex
have x R:
    x > 100
```

仅限新实数见证与良定义实表达式之间的一次比较，不是无限制见证搜索。

**内置语句**是执行器作为原始上下文动作理解的形式。例如 `have` 引入对象，`forall` 检查全称事实，`claim` 和 `thm` 证明可复用事实，`witness` 证明存在事实，`by cases` 组织分情况证明。它们不是普通数学对象，而是扩展或查看当前上下文的证明脚本动作。

**内置验证规则**不同于存储定理。它是能关闭当前目标的小型验证模式，常通过等价形式或常规计算。例如目标 `x > y` 可使用 `y < x` 或 `x - y > 0` 等常见等价形式。

某些路线是 Rust 层验证规则，标准包也可提供导入的 `forall` 事实。用户效果类似：无需当前文件先证明局部引理，即可使用常见数学背景。

```litex
forall x, y R:
    x - y > 0
    =>:
        x > y

forall x, y R:
    y < x
    =>:
        x > y

forall x, y R:
    x != y
    =>:
        y != x
```

最后的证明使用单前提的“不相等对称性”内置规则。输出保留已知 `x != y` 的证明为子节点；只读查找不能在任何方向都未知时凭空生成不相等。

内置验证规则也覆盖计算式事实：

```litex
1 + 2 = 3
```

普通数学书写隐含许多小等价与计算。没有内置规则，用户须手写每座桥：把 `x > y` 转为 `y < x`，再转为 `x - y > 0`，引用 `1 + 2 = 3` 的算术定理等。Litex 让用户写有意义的步骤，验证器承担有限的常用背景推理。

例如，`a Z` 时 `(a % 8) % 2 = a % 2` 能验证，因为外层模数 `2` 整除内层模数 `8`；不会泛化到 `3` 和 `8` 等不兼容模数。

边界来自结构，而不是节点预算。直接内置规则只有一层：前提可引用已知非 `forall` 原子事实或使用确定性计算，不能调用另一内置规则。独立内置策略只沿严格变小的受支持语法树递归，例如嵌套算术载体、求和、乘积、有限集构造器、有限乘积逐点合同性、集合成员关系或元组坐标。每层策略可在直接子节点尝试一层新的直接规则。两条路线都不调用已知 `forall` 匹配、具体定义、用户策略或完整验证器。Detailed 输出区分 `builtin rule` 与 `builtin strategy`，把嵌套子结果返回根节点。

有限区间是代表性示例。已知或可计算的端点序走直接快速路线。否则 `closed_range(a, b)` 的非空性结构性归约到 `a <= b`，`range(a, b)` 的非空性归约到 `a < b`。闭实区间 `'[a, b]` 用弱序，有任一开端点的实区间用严格序。更小的序子目标获得一层新直接规则，因此局部界如 `2 <= n` 能证明从 `1` 开始的索引载体合法，而不允许无限验证器递归。

有限乘积直接规则也识别逐点乘法与沿已知双射的拉回，不搜索或构造双射。

有限和中，闭整数区间上的带保护逐点相等可证明相应和相等。整数平移重索引在平移边界后可使用同类事实。两者都不创造双射，也不假设声明区间之外相等。

`reduce` 与 `finite_set_reduce` 是一般对象，但与既有数学词汇相连。操作为逐点加法、种子为 `0` 时，桥接到 `sum` 与 `finite_set_sum`；乘法/`1` 桥接到对应乘积。操作可由用户定义：已验证的具体 prop 展开后提供 `forall x, y T: op(x,y) = x + y` 即可。逐点 `forall x S: f(x) = g(x)` 提供合同性，已知 `$bijective` 提供有限集重索引。检查器使用这些事实，不创造它们。

区间归约记住顺序，因此重索引更严格。等长整数区间无需操作规律即可平移：当 `a <= b` 且 `b-a = d-c` 时，`reduce(a,b,f,op,s)` 等于 `reduce(c,d,fn(k Z) T {f(a+(k-c))},op,s)`。取 `c = 0` 可重定基准到 `0...(b-a)`。也可剥离首末端点，按左折叠顺序传递累加器种子。裸 `$bijective` 不足以反转或置换索引；验证结合律和交换律后，可通过 `finite_set_reduce` 使用无序路线。

一般不交并规律只保留一份种子：已知 `intersect(A,B) = {}` 后，`F(union(A,B),s) = F(A,F(B,s))`。看似更熟悉的 `op(F(A,s),F(B,s))` 将 `s` 计两次，除非有额外单位元假设，否则为假。种子 `0` 加法或种子 `1` 乘法，应桥接到既有有限和/乘积对象，使用专门规律。

有些常见一步蕴含本身就是直接规则。例如已知 `n $in N` 和 `n > 0` 直接建立 `n - 1 $in N`，无需第二次内置调用先推导 `1 <= n`。已知 `n $in N+` 也直接建立此结论。正数结果载体还需 `n > 1`，才可证明 `n - 1 $in N+`。同样，已知整数 `a`、`b` 与 `a < b + 1` 直接建立 `a <= b`，这就是常见等价 `a <= b <=> a < b + 1` 的离散相邻桥接。

函数资格来自存储事实，而不是引入名称的语法。已知 `g $in fn(x R) R` 允许类型正确的调用；索引在 `g` 上、与匿名函数相等的已知等式提供函数体。例如：

```litex
have fn f(x R) R = x + 1
let g = f
g = fn(t R) R {t + 1}
g(4) = 5
```

显式等式把函数体发布到 `g`。最后一行读取精确性质，再检查 `4 + 1 = 5`，不追随别名链。仅成员关系没有函数体信息。未知函数体、无效参数或失败的局部证明步骤不能建立具体返回值。默认 struct 字段名仍遵循定义选择的视图。

构造器和定义策略保持局部。它们可检查依赖元组是否为 struct，经一次已检查构造器投影可调用字段，或展开一个字面/已检查/模板集合构造式，或一个精确索引的命名构造式以检查成员关系。不扫描所有局部命名定义。

`struct` 的 `<=>:` 块中，等价事实形成有序局部过滤上下文。每条事实通过良定义性后暂存，不进行定义推导，所以先前 `value != 0` 可使后续 `1 / value` 良定义。交换顺序仍失败。定义时和检查实例化 struct 载体时使用同一有序检查；临时事实不泄漏到外围环境。

相等与其他原子事实共享搜索级别上限。存储事实、身份/alpha 与存储相等路径，再加闭合精确计算与结构成员关系，构成第 0 级（`Direct`）。特殊性质前提用第 0 级；内置前提用第 1 级；策略与定义/forall 前提用第 2 级。最高级改写只可用一次。数值与原子改写保留残余目标级别；直接函数值等式代换将残余限制在 Strategy，避免继续一般定义/forall 展开。WD 始终必需，继承当前上限。独立策略/深递归预算已移除。

闭合计算分支不查询存储数值代表元，也不展开函数。它计算闭合数值相等、实数序和标准集成员关系，以 `by_closed_calculation` 记录精确值。例如受限前提可使用 `1/3 < 1/2`。给定 `a = 2`，`a+1=3` 仍需独立代换路线。真值搜索前始终检查 WD：`1/0=1/0` 仍无效。[Direct 示例](../examples/proof_nodes/equal/direct_closed_calculation.lit)中的有限枚举无需先断言数值成员关系。这不解决全部剩余组合/几何失败；见[当前记录](../src/execute/execute_fact_stmt/builtin_entry_verification.md)。

Direct 也可执行确定性载体组合。`n in N` 时，`((n+1)+1)+1 in N` 通过遍历加法树成立，不为每个构造器额外消耗搜索级别。`floor(x)+1 in Z` 同样读取已检查 floor 陪域与加法封闭性。每个叶节点引用已有类型，或使用闭合计算/固定内置签名，不调用 SP 或完整搜索。叶类型缺失仍失败，全部对象 WD 义务仍必需。见[结构载体示例](../examples/proof_nodes/atomic/direct_structural_membership.lit)。

完整相等目标另外复用同一构造器匹配器，允许对应子等式使用有界内置/相等验证器。函数应用从末尾参数组向前对齐，因此 `f(a, b) = g(1, 2)(a, b)` 归约为函数部分 `f = g(1, 2)` 和对应参数等式。已知事实查找可通过只使用已知事实的合同路线传递另一谓词，但不隐式启动更完整的子证明路线。

整数检查也识别两个精确单点区间：`n <= x < n + 1` 关闭 `x = n`，`n < x <= n + 1` 关闭 `x = n + 1`。完整载体 alpha 等价的函数相等应使用 `by fn_extension`，在整个定义域建立逐点全称事实。结果存储普通相等 `f = g`，构造器合同性可在 `power_set(f) = power_set(g)` 等事实中复用。仅在真子集上一致不足以证明全局函数相等。旧 `$fn_eq` 与 `$fn_eq_in` 已移除。

函数元数据的查找比普通相等证明更窄。签名、函数体、返回载体和有限坐标使用已检查声明及索引在精确对象上的性质，不搜索相等类。例如：

```litex
have fn step(x R) R = x + 1
let alias = step
alias = fn(t R) R {t + 1}
alias(3) = 4
```

第三行证明并发布 `alias` 上的函数体，最后一行读取该直接性质。签名成员关系只发布可调用性，不发布数值函数体。模板实例从声明读取。这样元数据查询无需重建全部可见相等的图；普通相等证明仍可建立显式端点。

严格正前提也证明平方根非零：`x > 0 => sqrt(x) != 0`。仅 `x >= 0` 不触发规则。

规则需要全称、存在或复合前提时，使用显式保留内置定理调用，如 `release thm set_builder_member(x, B)` 或 `release thm tuple_equal_from_coordinates(L, R)`。调用用完整验证器检查要求，失败时不提交结论。规范有理数接口为 `release thm rational_has_unique_reduced_fraction(q)`。已知 `q $in Q` 时，存储 `exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}`。名称是无前缀保留名称，精确接收一个参数。此结论只经显式定理处理器可用；直接写存在陈述不会触发隐式最简分数规则，也不需要可信 `std/basics` 定理。

有限集基础也有显式接口。检查 `A $subset B` 且 `B` 有限后，可调用 `release thm subset_of_finite_set_is_finite(A, B)`。若上集合的有限证书已在受限存储/结构阶段可用，存储包含关系现在也发布下集合有限性。前向后果使后续大小表达式通过 WD，不开启更深搜索。无该证书时，仍需显式定理或现有有界策略。[推导示例](../examples/infer/atomic/subset_finite_upper_bound.lit)展示边界。有限 `s` 上，`release thm finite_set_has_bijective_index(s)` 存储 `finite_seq(s, finite_set_size(s))` 中的非规范存在索引，且从 `closed_range(1, finite_set_size(s))` 双射。这些是无前缀内核名称，不是 `basics::` 定义；任意有限序列不会因此被定义为双射。

为兼容旧源码，裸 `by thm name(args)` 仍是 `release thm name(args)` 的解析别名，遵循相同的全部结论执行路径，规范显示为 `release thm`。新代码裸调用用 `release thm name(args)`；选择一条原子推论时用带 `=>` 的 `by thm`。

只让一条原子推论向外发布时，用预览形式 `by thm name(args) => atomic_fact`。目标必须匹配该实例直接返回的原子结论，包括显式合取或相邻链分量。允许结构身份和绑定变量重命名；独立计算、环境事实、改写、等式反转和结论组合不能替代匹配。证明引用返回结论。只将所选事实提交到父环境；其正常推导后果仍可存储。所选事实必须在父环境良定义，复合目标和证明体会被拒绝。组合结论用 `release thm` 加独立证明步骤。选择仍要求箭头；只有独立的旧裸别名省略箭头。

数学定义同样使用显式 `by def A $subset B` 和 `by def $injective(A, B, f)`。新代码用行内形式；旧 `by def:` 加一个 `? fact` 目标仍为兼容接受。顶层验证入口中，裸的肯定具体谓词还可在已知 `forall` 匹配和用户策略之前，从定义各项证明。需要显式路线和输出时 `by def` 仍有用。即使目标已知，执行入口也要求定义展开；只有展开后的义务用普通搜索。因此真算术比较或 SetBuilder 成员关系并不会变成受支持的 `by def` 目标；应直接书写事实。

便利性也是信任边界的一部分。内置对象、内置事实、内置语句行为与内置验证规则都需要测试、示例和便于审计的输出。它们不是隐藏魔法，而是短 Litex 证明所依赖的内置数学接口。

<a id="if-there-are-ten-thousand-forall-facts-will-proving-one-proposition-become-slow"></a>

## 如果有一万条 `forall` 事实，证明一个命题会变慢吗？

如果同一上下文中一万条全称事实都是自动匹配的活动候选，就可能变慢。Litex 用已知事实、内置规则、代换与已知 `forall` 论证后续事实。这让用户能直接写目标数学事实，但也意味着不能把活动上下文视为无限制的全局搜索空间。

设计上主要有两个回答。

首先，应该显式调用的命名定理用 `thm`。它证明并存储命名定理，不把 `forall` 主体加入普通自动匹配事实。使用时写 `release thm name(args...)`，使大型、经典、昂贵或参数敏感的结果成为显式证明依赖，而非背景噪声。

其次，把广泛数学背景组织到源码局部引用包。群定理应放在需要它的源码旁，实分析定理应放在分析源码旁。所属模块在真正需要时才通过 `litex.config` 导入。这样活动的已知事实和已知 `forall` 空间更贴近当前主题。

<a id="can-an-imported-packages-public-symbols-be-used-without-the-module-prefix"></a>

## 导入包的公开符号可以省略模块前缀吗？

不可以。跨模块引用始终使用 `A::b` 或 `basics::theorem` 等规范限定名。模块名与符号名分开，因此 `A` 仍可同时是模块头与局部对象。交互终端导入也只支持限定名，且不能写在 Litex 源码中。

导入别名属于导入包自己的 `litex.config`。两个包可以各用 `Common = "./dep"` 指向不同目录；引用经各自清单与规范化路径解析。同目录的两个别名共享模块；同一清单内重复别名仍被拒绝。全局显示标签与本地别名分开。

实用规则：

- 目标形状明显揭示实例化的短小、局部、常用事实，使用自动 `forall` 匹配；
- 辅助结果应作为局部可复用上下文时，使用带 `? forall ...` 目标的 `claim:`，或直接 `forall`；
- 全部结论都应可见时，用 `thm` 加 `release thm`；只让一条原子推论向外发布时，用选择 `by thm ... => fact`；
- 未完成背景放在源码局部引用包，只导入当前文件需要的事实。

这不只是性能问题，也关乎可读性。数学上重要的事实通常直接命名会让证明更清楚。

<a id="what-is-a-type-in-litex"></a>

## Litex 中的类型是什么？

Litex 的“类型”主要是集合论参数标注，不是依赖类型论中的类型。

`have x R`、`forall x R:` 或 `exist x R st { ... }` 中，`R` 表示 `x` 是具有 `x $in R` 成员事实的对象。同样适用于 `Z`、`N`、`{1, 2, 3}`、`cart(R, Z)`、`power_set(S)` 等普通集合对象。标注提供良定义性信息和后续步骤可匹配的事实。

某些标注是参数种类，而非普通集合定义域。例如 `have A set`、`have B nonempty_set` 和 `have c finite_set` 引入名称并记录 `$is_set(A)`、`$is_nonempty_set(B)`、`$is_finite_set(c)` 等事实。不是说 `set` 是包含所有集合的巨型集合，而是引入具有相应集合论性质的数学对象的表层形式。

To-Lean 目标把这一区别保留为证明证据：量化 `A set` 获得显式 `hA : Litex.IsSet A`，普通 `x A` 获得从 `hA` 选出的精确集合代表元中的成员关系。`Litex.Set` 是 Lean 的精确载体表示类型，不是源码全集；所以 `A $in Litex.Set` 或把 `$is_set(A)` 抹成 `True` 都不是忠实翻译。

函数“类型”也是集合论函数空间。`fn(x S) T` 表示输入来自 `S`、值来自 `T` 的函数对象。每个普通函数参数定义域必须是固定集合对象：后面的对象定义域不能引用同一 `fn` 签名前面的参数（所以拒绝 `fn(x R, y S(x))`）。返回集合与 `: domain conditions` 可以引用函数参数；调用把实际参数代入这些集合表达式。定义域与返回集仍是普通集合对象。`set`、`nonempty_set` 和 `finite_set` 等更宽参数种类属于定义或定理头部（其中 `forall S set, x S` 按序绑定，允许），不能作为普通函数输入定义域。因此 `fn(x set) R` 不能表达“接受任意集合的函数”。集合论函数在每个参数位置都需要一个具体定义域对象，Litex 不把“所有集合的集合”当普通集合对象。

重要后果是：对象没有决定后续全部记号的唯一规范类型。同一对象可以已知属于多个集合。Litex 用当前已验证的成员关系、函数空间与集合性质事实判断表达式是否良定义、后续事实能否证明。

<a id="why-does-litex-emphasize-relationships-instead-of-construction-ancestry"></a>

## 为什么强调关系，而不是构造谱系？

熟悉对象常有多种构造。整数可由自然数对构造，有理数由整数对构造，实数由柯西序列、戴德金分割、十进制展开或其他等价方式构造。Litex 不要求普通用户每写 `Z`、`Q` 或 `R` 都继承全部构造历史。

Litex 优先考虑关系。内核与源码局部包可以暴露对象及其有用关系：成员、算术、序、稠密性、floor 界、完备性、函数空间、集合操作等。日常证明中，重点常不是 `R` 从 `Q` 的精确构造，而是 `Q` 嵌入 `R`、有理数在实数中稠密、实数柯西序列收敛，以及非空有界实数集有上确界。

这是有意取舍。内置 `R` 是具有验证器可见性质的数学表层，不是宣告“该对象沿精确商与完备化链构造”的证明项。需要有理数稠密性或实数完备性的源码，应在可见的源码局部引用包陈述背景，记录每个 `trust` 边界，而非加载全局数值库。

实用规则：

- 只需要通常关系时，直接使用 `Z`、`Q`、`R` 等内置对象；
- `Q` 在 `R` 中稠密、`R` 完备等广泛语义背景放在源码局部引用包，显式呈现信任边界；
- 章节或领域特有定理保持局部，直到值得提取为复用包；
- 只有构造本身就是数学主题时，才显式形式化构造。

Litex 不是反对基础，而是为普通数学选择更轻的用户路线：暴露实际使用的关系，并让可信背景事实足够显式以供审计。

<a id="does-litex-define-r-from-q"></a>

## Litex 从 `Q` 定义 `R` 吗？

不。当前 `Q` 与 `R` 是内置载体对象。Litex 记录它们之间的数学关系，但内核不说 `R` 的元素字面上由 `Q` 对象的等价类构成。

Analysis I 翻译具体展示这一区别。陶哲轩原书用有理柯西序列的等价类定义实数。Litex 章节保留内置 `R`，引入 `$has_formal_limit_in_Q(a, x)`，表示有理柯西序列 `a` 代表内置实数 `x`。定理 `cauchy_sequence_representative_in_Q_exists` 陈述每个内置实数有这种代表。这是表示或兼容定理，不是 `R` 的定义；教材中证明目前是显式 `trust` 边界。

柯西序列构造只是实数的一种表示。其他标准方式包括：

- `Q` 的戴德金分割；
- 嵌套有理区间；
- 无限十进制展开，并认同 `0.999...` 与 `1.000...` 等表达；
- 由泛性质刻画的 `Q` 完备化；
- 包含 `Q` 的公理化完备阿基米德有序域。

要完整连接内置 `R` 与有理柯西表示，需要检查过的接口陈述：

1. 每个有理柯西序列代表唯一实数；
2. 每个实数都有有理柯西代表；
3. 两个有理柯西序列等价，当且仅当代表同一实数；
4. 代表元上的加、乘、序与 `R` 上对应操作一致。

有该接口，可说内置 `R` 与 `Q` 的柯西完备化在相关有序域结构下同构，仍不应说两者定义上是同一对象。前一章也有同样区别：整数分数可以代表内置有理数，不使内置 `Q` 定义等于整数对的商。

构造本身是主题时，Litex 可以形式化具体构造。默认内置接口只是不强制所有后续用户继承唯一的构造历史。

<a id="are-sin-cos-tan-and-cot-numerical-functions"></a>

## `sin`、`cos`、`tan` 和 `cot` 是数值函数吗？

当前 beta 中，它们是原生符号实数对象，参数是以弧度计的实角。验证器知道小型中央接口，并通过一个规范化器推导奇偶性、差角与倍角公式、选定 `pi` 值、周期性、余函数公式和范围界。

`sin` 和 `cos` 在 `R` 上全定义。使用 `tan(x)` 要求 `cos(x) != 0`，`cot(x)` 要求 `sin(x) != 0`；无定义表达式在相等检查前的良定义性阶段失败。预览仍是符号式的：`eval` 与 Python 提取明确拒绝原生三角表达式。当前解析器也接受实数 `arcsin`、`arccos`、`arctan`、`arccot`，定义域与主值范围规则见[手册](Manual.md#native-real-trigonometry-beta-preview)。`pi` 的精确有理系数可建立主值范围比较，无需小数近似。四分之一角反函数示例使用正向值与显式右逆等式链；`arccot(-1)=3*pi/4` 遵循 `(0,pi)` 分支。这不是复三角或数值求值接口。Lean 编译未连接到当前 Cargo 构建；见 [CLI 边界](cli_zh.md#lean-compiler-boundary)。

<a id="does-the-native-c-scalar-system-turn-every-number-into-a-complex-value"></a>

## 原生 `C` 标量系统会把每个数都变成复数值吗？

不会。当前 beta 中，`C` 是最大的默认标量载体，标准集合满足 `N ⊆ Z ⊆ Q ⊆ R ⊆ C`。验证器仍保留能建立的窄结论。整数算术仍是整数算术，实数算术仍是实数算术；没有更窄的受支持载体时才回退到 `C`。

`C*` 表示非零复数载体 `C \ {0}`。因此 `R* $subset C*`、`C* $subset C`，`have z C*` 提供 `z $in C` 与 `z != 0`。反向包含 `C $subset C*` 为假，`0 $in C*` 被拒绝。

这也说明复数相等不引入复数序。`<`、`<=`、`>`、`>=`、符号推理、实区间、`abs`、`sqrt` 和 `log` 仍要求实操作数。`C_abs` 是独立复数模，结果为非负实数。

本版本原生复数层仍是符号式的。验证现在也进行带 `i * i = (-1)` 的有界精确多项式/有理式规范化，因此 `2 * i + 1 = i * i + 2 + 2 * i` 与 `(1 + i) * (1 - i) = 2` 等恒等式直接通过。除法仍需普通非零 WD 证明。`eval` 与 Python 提取不会因此取得复数运行时表示。

早期 Lean 产物描述独立复数规范化后端，不确立当前 `src/` 流水线的编译覆盖。`C`、`i`、`re`、`img`、`C_abs` 是保留原生形式；把它们用作普通标识符的源码须换名。见[复数标量参考](Manual.md#complex-scalars-beta-preview)。

<a id="why-not-just-import-a-big-library-and-cite-the-theorem"></a>

## 为什么不直接导入大库并引用定理？

许多成熟证明助手项目中，导入大库并引用最强可用定理是最高效路线。这是大型库系统的真实优势。

Litex 面向不同工作流，尤其教材与教育。形式化微积分或分析教材时，脚本最好展示教材教授的推导：定义、局部引理、中间事实，以及后续结果如何使用前文。若主要工作变成“在数学字典中找定理并引用”，结果或许通过，但代码记录的是结果已存在在哪里，而不是学习路径。

因此 Litex 尝试让基础数学成本足够低，使用户能直接书写原书证明。内置对象与小型背景接口让文件无需庞大导入即可开始。较大包仍重要，但应提供可见背景或可复用接口，而不抹去当前章节的核心证明。

这不是说导入不好，而是讨论数学工作应在哪里。教材优先形式化中，证明脚本应是推导，而不只是定理数据库的指针。Lean 或 Isabelle 的大库路线常是优秀形式化工程。Litex 探索更轻基础是否能让原书证明足够便宜，可直接写下并检查。

<a id="why-can-an-elementary-looking-result-still-need-a-cite-interface-or-explicit-trust"></a>

## 看起来初等的结果，为什么仍需引用接口或显式 trust？

普通数学文字省略大量支持设施。这不使结果无法形式化，也不使未完成 Litex 证明成为语言失败，而是文件必须说明原文默认了哪个接口。成熟库常已有许多接口，源码局部发展未必已有当前定理需要的接口。

例如：

- 非空有限 `R` 子集有最大值，可能需要有限集归纳或枚举接口、非空见证和插入一个实数保持选定最大值的事实。
- 原生 `gcd(a, b)` 对不全为零的整数对可用。讲解其构造的教材仍可定义 `gcd_by_finite_divisors` 等名称透明的源码函数，证明规格并桥接到原生 `gcd`；见 [`gcd_from_finite_divisors.lit`](../examples/_internal/regression/gcd_from_finite_divisors.lit)。
- 原生 `$coprime(a, b)` 遵循初等 `Nat.Coprime` 表层，无需导入 `std/basics`，对全部自然数对可用，在 `(0,0)` 为假。整数与一般环互素仍是独立接口。
- `|S union T| <= |S| + |T|` 可能需要基数接口：分解为不交部分，或以单射/双射论证呈现重叠。

不要仅因结果显然就整项标 `trust`。保留源码定理，做最小自然尝试，记录精确缺失桥接与验证反馈。一次性桥接保持最小局部证明债务。同一背景事实确实反复出现时，才提供命名源码局部引用接口。含义稳定且多个独立使用表明它确是常用背景后，再考虑共享 `std` 接口。其余源码证明尽量保持已检查。

<a id="what-are-the-boundaries-of-litexs-type-system"></a>

## Litex 类型系统有哪些边界？

Litex 有意不追求 Lean、Coq 或 Agda 意义的完整依赖类型论。表层更接近集合论普通数学：对象属于集合，结构是带命名视图的笛卡尔积子集，谓词表达性质，证明扩展已验证事实上下文。

函数参数定义域与返回集相对于当前签名固定。可使用已经绑定的外围载体，如 `forall q set` 后接 `fn(c1, c2 q) q`，但不能使用同一函数自己的参数。因此 `fn(S power_set(R), x S) R` 和 `fn(S power_set(R)) fn(x S) R` 在解析时被拒绝。定义域条件和函数体可依赖参数，如 `fn(x R: x > 0) R {x + 1}`。更精确的结果性质用单独事实表达，不用参数索引返回集。

解析器解析参数载体时延迟注册函数参数，解析完整返回对象时移除暂时可见性。WD 独立执行同样边界。普通 `forall`、`exist` 保留按序依赖；`template` 支持按任意载体或假设索引的结构、序列空间、商构造等族。Litex 仍不暴露 universe 多态类型族、证明索引计算类型，也不把证明项作为普通计算数据。

具体商群构造见手册的商群部分。

<a id="what-is-a-struct-in-litex"></a>

## Litex 的 `struct` 是什么？

`struct` 不是有隐藏字段的类或记录对象，而是笛卡尔积子集的命名视图。字段名标记积中的位置。

结构至少声明两个字段，没有单载体的单字段“身份视图”（解析错误：`struct definition expects at least two fields`）。

例如：

```litex
struct FirstQuadrant:
    x R
    y R
    <=>:
        x > 0
        y > 0

release thm struct_member((1, 2), &FirstQuadrant)
have p &FirstQuadrant = (1, 2)
p.x = 1
p.y = 2
```

可读为 `cart(R, R)` 上的命名集合构造式：

```text
&FirstQuadrant = { p in cart(R, R) | p(1) > 0 and p(2) > 0 }
```

字段 `x` 标记索引 `1`，`y` 标记索引 `2`。`p` 直接在 `&FirstQuadrant` 中定义，所以 `p.x` 为第一分量，`p.y` 为第二分量。直接 `p &FirstQuadrant` 绑定是唯一自动性质释放情况：打开一层 struct，存储笛卡尔积成员关系、普通字段/坐标桥接、字段载体和规律。

其他由定义拥有的 struct 表达式，写 `release struct def expression`。语句先验证精确表达式属于已定义的 struct 载体，再释放恰好一层。没有 `as &Struct` 语法，也不递归打开。例如 `make_outer(t)` 返回 `&Outer`，`Outer.inner` 定义为 `&Inner` 时，`release struct def make_outer(t).inner` 打开 `Inner`，不打开 `Outer` 或 `Inner` 下的任何结构。

多字段值 `e` 打开后存储精确笛卡尔积成员关系及 `e.x = e(1)` 等式，连同字段载体与规律。不存元组形状或维度事实。这些元组/结构桥接不在其他位置存储，只有结构成员验证器可在检查时内部使用元组表示。

参数化结构的 `&Name<a>` 是实例化结构集，无参数结构的 `&Name` 是结构集。两者都是普通集合，在任何要求集合的绑定或函数签名位置都合法。

同一元组可属于多个结构集，但字段选择不因此歧义：命名字段属于符号或函数返回值的定义。新绑定的载体 `p &FirstQuadrant` 固定 `p` 的所有权，没有在单次使用处改变视图的表层形式。

同一规则支持连续字段链。`outer &Outer` 且 `Outer.inner` 直接定义为 `&Inner` 时，`outer.inner.value` 合法。中间字段所有者来自字段定义，不来自证明搜索。命名集合定义或后来的 `outer.inner` 属于 `&Inner` 事实不会增加字段。

这种合法性只表示良定义性。查找 `outer.inner.value` 检查定义字段路径存在，不存储字段成员、字段/索引等式或实例化结构规律。定义现在发布对参数和实例的全称规律，展平后件全称陈述，同时保持条件和存在见证作用域。载体与前提验证后，普通已知 forall 匹配可使用规律，包括嵌套实例。用 `release struct def outer.inner` 实体化表示与性质事实。函数显式 struct 返回载体使 `f(t).field` 合法，但不自动打开结果。

定义提供载体时，后缀可组合。最后字段可调用，因此 `scalars` 是结构值字段且 `mul` 可调用时，支持 `space.scalars.mul(a, b)`。同样，`have fn make_inner(...) &Inner = ...` 后，`make_inner(...).value` 合法。

这不是唯一名义类型，也不从全部已知成员关系推断字段。后来的 `p $in &FirstQuadrant` 只提供成员命题，不立即存位置后果、规律或 `p.x`；也不能用 `release struct def p` 打开，因为 `p` 没有定义拥有的 `FirstQuadrant` 视图。`p &Point` 也属于 `&ComplexPair` 时，`p.x` 仍是定义固定的 `Point` 字段。要使用另一套名称，显式引入新对象，如 `have p2 &ComplexPair = (p.x, p.y)`，再写 `p2.real`、`p2.img`。

<a id="why-would-a-vector-space-own-its-scalar-system"></a>

## 为什么向量空间应拥有自己的标量系统？

它让普通单空间接口更小，也更忠于数学。一个 `VectorSpace<s,V>` 从选定结构暴露 `space.zero`、`space.smul(a,v)`、`space.scalars.mul(a,b)`。同样模式让内积空间拥有标量几何与向量空间操作。

这不会默许任意空间兼容。连接两个空间的关系，如 `is_linear_map(Vspace,Wspace,T)`，记录一次 `Vspace.scalars = Wspace.scalars`。双线性、张量及其他多空间关系用同样边界。多项式算术等纯标量构造仍显式接收 `ScalarSystem`，因为那里没有向量空间所有者。

<a id="why-can-an-anonymous-function-be-written-as-fnx-r-r--x"></a>

## 为什么匿名函数可以写成 `fn(x R) R {(-x)}`？

这是有意的简写，不是笔误。完整显式形式 `fn(x R) R { (-x) }` 表示参数 `x` 属于 `R`、返回集合是 `R`、函数体是 `(-x)`。

参数定义域都与返回集相同时，也接受紧凑形式 `fn(x R) R {(-x)}`。同样，`fn(x, y) R {x + y}` 表示两个输入都属于 `R`、返回集为 `R`，是 `fn(x R, y R) R { x + y }` 的紧凑形式。

紧凑形式适用于短数学表达式，如向求和传 `fn(x R) R {x}`，或把 `fn(x R) R {(-x)}` 用作群逆运算。解释文档或定义域与返回集容易混淆时，显式形式通常更清晰。两者都是普通匿名函数对象，可以按函数相等规则比较。

<a id="why-does-litex-have-template"></a>

## 为什么有 `template`？

`template` 用于对集合、结构或满足条件的载体等参数统一的定义，而这些参数不能建模为单个普通集合论函数的输入。

可以这样读：先假定尖括号参数已引入并满足头部条件，再在临时上下文执行模板体中的普通定义语句。通过后，Litex 将结果存为族。后来写 `\name<R>` 等实例时，代入具体参数，得到相应定义对象或函数。

例如：

```litex
template<s set>:
    have carrier_copy set = s

\carrier_copy<R> = R
\carrier_copy<Z> = Z
```

先固定任意集合 `s`，临时上下文中 `carrier_copy` 可定义为 `s`；对每个 `s set` 都成立，所以之后可调用 `\carrier_copy<R>`、`\carrier_copy<Z>` 等。

已检查模板也发布普通定义体提供的事实，对尖括号参数全称量化，把头部条件保留为前提。例如：

```litex
template<S nonempty_set>:
    have member S
\member<R> $in R
```

模板存储 `forall S nonempty_set: \member<S> $in S`，普通已知全称搜索便可提供实例成员关系。同样适用于对象等式与所选见证性质、函数签名与带保护方程、唯一存在选择和替换事实。发布的是定义存储，不是临时作用域假设或证明中间步骤。见[验收示例](../examples/stmt_nodes/definition/template_definition_facts.lit)。

最简单理由是：函数输入必须来自特定定义域集合，但 `set` 本身不是特定集合，而是“引入参数并检查它是集合”的表层参数种类。因此对每个集合定义的族应把集合放在定义头部，不藏成假的函数参数。

实例以尖括号保持参数可见。族若为 `template<s set>:` 且主体为 `have name ...`，在 `R` 的实例写 `\name<R>`，在 `Z` 的实例写 `\name<Z>`。选择的集合伴随名称，每次使用都能看清所属载体/参数，不同实例不会混淆。

普通数学中此模式很常见：

- `seq(S)` 概念上是按值集 `S` 索引的族；`S` 上的序列本质是正整数到 `S` 的函数，不是对所有值集的唯一通用函数类型。
- 群结构是载体集合上的族。`&Group<R>` 与 `&Group<Z>` 是不同结构载体集，因为载体是数学数据的一部分。
- 商构造自然是具体群及相关正规性/等价假设上的族，不是从“所有群”到集合的单个全局函数，而是参数应保持可见的参数化构造。

`template` 让 Litex 在保持集合论基础时直接表达数学族。普通函数用于定义域是已知集合的映射，模板用于参数应附着于每个实例的数学族。

例如 `seq` 是内置对象形式，若自行定义同一思路，应定义函数空间族：

```litex
template<S set>:
    have my_seq set = fn(n N+) S

\my_seq<R> = fn(n N+) R

```

实例化集合相等通过。自动成员关系传递到该模板实例仍是缺口；以下目前软失败：

```text
template<S set>:
    have my_seq set = fn(n N+) S
have a fn(n N+) R
a $in \my_seq<R>
```

关键是 `S` 不是普通函数输入，而是族参数。实例化后 `\my_seq<R>` 是普通实值序列集，即 `N+` 到 `R` 的函数。`\my_seq<Z>` 同理为整数值序列集。尖括号使每次使用的值集可见。

内置 `seq(S)` 仍可有特殊语法或验证支持；模板版本展示底层集合论形状：序列类型是参数化函数空间族。

<a id="if-ai-can-write-lean-proofs-what-is-litex-for"></a>

## AI 能写 Lean 证明，Litex 还有什么用？

AI 可以大幅降低证明器代码的生成成本，常能找到引理名、写 tactic、完成常规附加条件。这很有价值，但生成成本与理解成本不同。机器生成证明可以通过内核，数学家仍可能需要从大量面向系统的代码中重建简单数学思路。

Litex 检验持久产物能否更贴近数学思路。AI 补常规细节，已检查源码保留读者理解和修改论证所需的事实、见证、情况、定义与计算链。表层省略常规步骤时，验证输出仍应暴露论证它的规则、已知事实、定义、定理或显式假设。

这不声称 Lean 证明必定长或不可读。Lean 有强自动化和简洁、精心设计的接口。Litex 检验不同的默认接口：AI 让证明生成充足后，已检查数学能否保持可读？[Lean–Litex 代表性对比](Representative_Lean_Litex_Example_Comparisons_zh.md#ai-lowers-generation-cost-not-automatically-understanding-cost)中的 epsilon 乘积例子是具体测试：持久证明应保留短估计 `|x * y| = |x| * |y| < epsilon * epsilon <= epsilon`，同时保留
其附加条件可供审计。

<a id="what-is-fundamentally-different-about-litex"></a>

## Litex 最根本的不同是什么？

核心区别是匹配与代换的验证接口。

用户写数学事实：等式、成员关系、蕴含、存在见证、`forall`、函数事实、集合事实和 prop 事实。验证器判断它们能否通过内置规则、已知事实、已知 `forall`、定义、匹配和代换，从当前已验证上下文得出。

核心交互因而更接近：

1. 写下一条数学事实；
2. 让 Litex 将其与已验证上下文及可信数学背景匹配；
3. 成功后存储事实，继续扩展上下文；
4. 失败时查看缺的是事实、定理调用、库支持，还是论证本身的缺口。

这使证明常像普通数学文字或计算链。脚本暴露应成立的事实，检查器执行人通常默默完成的常规匹配与替换。

例如 `b - a > 0` 或 `0 < b - a` 已验证时，正差内置规则能对实数 `a`、`b` 证明 `a < b`。它读取保存的界并引用前提，不递归发现该界。`b - a >= 0` 不能支持严格序。[可运行示例](../examples/proof_nodes/atomic/by_builtin_rule/greater_from_positive_difference.lit)也覆盖对应 `>` 目标。

保存的负差给出互补实数序。弱目标接受更强的严格界，弱界绝不证明严格比较。固定负形式 `0-u`、`-u`、`(-1)*u`、`u*(-1)` 使用同样有界存储前提桥接。例如：

```litex
forall a, b R:
    a-b<0
    =>:
        a<b

forall u R:
    -u<0
    =>:
        u>0
```

Detailed 输出保留所选前提的实际方向、严格性与引用。这些叶规则不递归寻找差值界。见[带符号差示例](../examples/proof_nodes/atomic/by_builtin_rule/signed_difference_order.lit)与[负号示例](../examples/proof_nodes/atomic/by_builtin_rule/negated_sign_order.lit)。

已验证事实进入上下文时，某些常规后果也会保存。例如 `n $in Z` 后保存 `n >= 0`，同作用域发布 `n $in N`。更一般的 `b <= n` 或 `n >= b` 需要 `n` 的整数证书及可用的 `b` 非负证书。后续定义域为 `N` 的函数调用便能引用参数载体，包括归纳目标的 WD 检查。仅非负实值不支持 `N`，弱界不支持 `N+`。见[下界推导示例](../examples/infer/atomic/weak_integer_lower_bound_in_n.lit)。

实值函数的常规载体检查也能跨字段表达式组合。目标 `f(x)^2 / 4 <= f(x)^2 / 4` 在证明体运行前先要求分数为实数。构造器封闭内置规则以既有限制前提权限检查返回值叶与整数指数。除法仍需合法非零分母；仅复数返回值不获得实载体。[实构造器示例](../examples/proof_nodes/atomic/by_builtin_rule/real_arithmetic_constructor_closure.lit)保留该目标 WD 案例，针对性测试覆盖拒绝边界。`abs` 中的实值笛卡尔函数同样分工：外围 WD 检查参数定义域，算术封闭消费返回签名。[笛卡尔函数示例](../examples/wd/real_cart_function_arithmetic.lit)检查实差和带非零保护的商。

这不是魔法证明任意目标，而是把普通数学结构放进验证器和可见局部背景包，提供事实导向接口。取舍明确：可信实现比小内核证明助手更大，因此内置规则、推导规则、`trust` 与导入事实需要清晰边界、测试和便于审计的输出。

Litex 应被描述为 Lean、Coq、Isabelle 的补充，不是替代。它们提供更深基础与更大的成熟库。Litex 检验较窄假设：以匹配和代换扩展已验证上下文为主接口，能否降低许多普通数学论证的检查成本。

<a id="why-does-litex-think-of-proof-as-context-growth"></a>

## 为什么把证明视为上下文增长？

接口以事实为导向，证明通常是数学事实序列。验证后，Litex 把事实存进当前上下文，后续通过匹配、代换、内置规则或已知 `forall` 实例化使用。

例如：

```litex
have x R = 2
x + 1 = 3
```

第二行不是 tactic 脚本，而是用户所需数学事实。Litex 检查已知 `x` 为 `2`，将等式归约为普通数值计算，再存新事实。核心体验是：写下一条有用事实，让检查器解释成立原因，再从更强上下文继续。

裸 `have x R` 是从非空载体选择见证，与显式 `have x R = 2` 不同。当前运行时保留这些步骤的验证和存储证据，独立 Lean 重放需保留区别。早期编译器实验不由当前 `src/` 构建；此例不说明当前 Lean 覆盖。

精确存在陈述已知时，验证器在专门内置存在路线之前记录直接 `FactId` 引用。这样保留事实来源，不扩展普通存在证明搜索。

<a id="does-zero-premise-direct-evaluation-replace-every-symbol-by-an-equal-object"></a>

## 无前提直接求值会把每个符号替换成相等对象吗？

不会。直接求值按书写形式检查原子事实，不将所有参数经 `have x T = value` 定义展开，再对改写目标重试。

例如 `2 $in Z` 无前提直接求值，无需生成待证子事实。`have one Z = 1` 和 `have integer_set set = Z` 后，`one + 1 $in integer_set` 不会仅因参数都有闭合相等代表而成为直接求值。已知事实匹配仍可经已检查等式传递已证明事实，但不会对改写参数执行直接求值以制造该来源事实。

相等的无前提阶段还包括终止的结构合同性。已知 `x = y` 时，可逐构造器比较 `(x + 1) * (x + 2)` 与 `(y + 1) * (y + 2)`。这不使任意符号等式自动成立：没有已知叶 `x = y`，乘积相等仍未知。产生前提的数学相等规则只在这些无前提路线失败后尝试。

<a id="why-does-litex-distinguish-success-failed-and-sessionerror"></a>

## 为什么区分 Success、Failed 和 SessionError？

三者区分容易混淆的情形。

**Success** 表示从内置规则、已知事实、已知 `forall`、定义或其他已接受上下文找到证明路线（或完成定义），并将临时环境合并到父环境。

**Failed**（软失败）表示语句未成功，丢弃临时环境，继续会话。常见原因：

- 搜索失败：语句有意义，但证据不足；
- 良定义性失败：对象或事实尚不合法；
- 同一事务封装中的其他软语句失败。

软失败不证明命题为假。它可能为假，也可能只缺更小的中间步。批量 JSON 在 `statement_results` 内保留软失败，带 `"success": false` 与 `why_failed` 载荷。

**SessionError** 表示硬失败，会话必须停止。批量 JSON 将其暴露为顶层 `"session_error"`。

内部不变量冲突明确报告为 `internal_bug: Litex internal bug: <specific reason>`。这是实现错误，不是普通未证明语句。它停止会话；不会将受影响会话称为可安全继续，也不声称内部提交错误已原子回滚。

反馈因此更有用：搜索软失败通常意味着补缺失数学事实；WD 软失败意味着先修表达式或定义域再讨论真值；SessionError 意味着停止并修复会话不变量。

某些原子相等失败的证据树有更窄细节。已知相等停在 `trace(q) = base(q)` 等函数值前缀，目标却涉及 `trace(q)(row)` 时，会报告未匹配的外围应用与最近前缀，指导先投影或改写前缀，再应用剩余参数；不会执行新合同证明或接受失败目标。

<a id="does-a-tuple-call-supply-its-coordinate-carrier"></a>

## 元组调用能提供坐标载体吗？

字面和命名元组使用普通函数调用。所选坐标载体根据实际值或笛卡尔成员来源检查：

```litex
forall x,y N:
    (x,y)(1)=x
    (x,y)(1) $in C
```

此字面值也支持直接 `(x,y)(1) $in C`。`(x,y)(3)` 等无效输入在 WD 失败。笛卡尔集合相等不恢复构造维度或因子列表；元素成员关系提供完整函数定义域与坐标载体。

<a id="which-assumptions-are-available-when-checking-an-induction-target"></a>

## 检查归纳目标时有哪些假设？

`by induc n from base` 的目标 WD 使用 `n $in Z` 与 `n >= base`，不使用归纳假设。基础和步骤证明体随后在不同局部作用域经普通证明体检查器运行：

```litex
have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
    n $in N
    have a N = 0
```

`n >= 0` 使目标可调用，已检查 `n $in N` 也为后继应用提供自然数载体。基础改为 `-1` 会拒绝目标 WD。`by strong_induc` 相同；更强假设只在 WD 后的后继作用域提供。递归函数定义还要求每层嵌套情况列表覆盖父保护条件，兄弟情况互不相交，才能发布。

<a id="why-does-litex-check-well-definedness-before-truth"></a>

## 为什么先检查良定义性，再检查真值？

对象、定义域与附加条件有依据后，表达式才有意义。这在尝试证明或反驳事实之前发生。

函数应用参数必须属于定义域，除法分母必须非零。缺少这些事实时，应报告表达式问题，而不只是目标等式软失败。

`let` 引入的函数名不必直接携带签名。`let g = f` 后，WD 沿 `g` 到 `f` 的精确透明定义，复用 `f` 已检查签名，按 `f` 定义域检查实际参数。原子验证使用同样确定的单向归约并记录证据。这不是循环真值检查或相等类搜索：只跟随所查 `let` 符号的存储定义，WD 不启动一般相等或 `forall` 搜索。

许多数学错误不是假定理，而是形式不良的陈述：域外调用、错误笛卡尔积投影或缺附加条件。Litex 试图明确区别。

`have x S = value` 的载体兼容属于语句 `verify_process` 阶段，在存储 `x` 前运行。可建立标准数值来源载体时，错误同时报告所需 `S` 与来源载体。因此 Z 值余数报告 `required N`、`known Z`；后来的证明体不等式不能追溯地让失败定义成为 N 绑定。

<a id="can-a-predicate-premise-make-a-later-expression-well-defined"></a>

## 谓词前提能让后续表达式良定义吗？

能，前提是肯定的具体谓词，且已检查定义有所需后果。`forall` 前提列表或 `exist` 主体中，Litex 在临时作用域从左到右检查事实。每条检查后的事实在其中被假定，可在下一条之前暴露可靠定义后果。

若 `$nonzero_on(E, g)` 定义为 `forall x E: g(x) != 0`，后续匿名函数体可安全包含 `1 / g(x)`。定义恰好提供分母义务；无前提时，同一表达式因不良定义被拒绝。

这不是在判断语法意义时运行任意搜索，而是通过普通带保护推导展开肯定具体定义。递归定义有循环保护，`abstract_prop` 没有条款，量化检查结束时临时后果全部消失。

<a id="why-cant-an-existential-or-set-builder-body-contain-forall"></a>

## 为什么存在陈述或集合构造式主体不能包含 `forall`？

主体有意使用小型性质语法：原子事实、平坦合取、链和析取。主要工程原因是索引键：只有四形状时，`exist` 查找键易设计，已知存在搜索只是形状桶加精确或统一匹配。匿名全称会在复用于见证、匹配、构造式成员、代换和推导的主体内加入新绑定作用域。排除它可使键与所有消费者无歧义。

改为给量化条件命名：

```litex
prop is_reduced_fraction(p Z, q N+):
    forall z N+:
        p % z = 0
        q % z = 0
        =>:
            z = 1

have a Q
trust exist p Z, q N+ st {a = p / q, $is_reduced_fraction(p, q)}
```

`forall` 仍是普通事实，在 `prop` 定义内合法。只拒绝它匿名作为存在或集合构造式主体条目。

<a id="why-does-litex-have-both-claim-and-thm"></a>

## 为什么同时有 `claim` 与 `thm`？

二者都证明事实，但接口角色不同。

`claim` 适合短、局部、可复用上下文。证明后，其事实作为普通上下文供后续使用，适合应像当前数学环境一部分的辅助事实。

`thm` 适合重要命名结果，让使用可见。按名称存储，显式 `release thm name(args...)` 使用，避免大型、经典、参数敏感或源码包结果静默变成背景搜索噪声。

区别部分是性能，主要是可读性。数学上重要的结果，在使用点命名通常更便于审计。

<a id="is-proof-debt-a-proof"></a>

## 证明债务是证明吗？

不是。`trust` 是显式注入假设，不产生证明。它最接近 Lean 的 `by sorry`，有意让作者跨越普通证明边界。例如以下两项都是有意的 `trust` 用法，不是验证器错误：

```litex
prop positive_real(x R):
    x > 0

trust 0 = 1
trust $positive_real({})
```

第二行即使此前不知道 `{}` 属于 `R` 也接受。具体 `prop` 参数载体是正常使用定义时的证明条件，不是限制 `trust` 可注入内容的形成检查。可信命题存储后，普通定义推导也可能记录参数事实，此处为 `{} $in R`，以及其他定义后果。它们是不安全假设的后果，不是独立检查的发现。

因此 `trust` 有意很强。仍要求可解析源码、已知谓词且元数正确，以及运行时可表示的参数对象，不能提交任意畸形语法。但可假设错误等式，把对象放在命题先前载体之外，并让后续在可信上下文中成功。收紧具体命题调用以拒绝这种可信参数，会削弱预期逃生口，所以不应归类为 WD 错误。

文档与审计中，`trust P` 应读为“从此假设 P”。后续 `verification` 轨迹引用来自 `trust` 的事实，只解释其如何从注入假设得出，不说明该假设已由 Litex 证明。

`trust` 行成功也仅表示假设被接纳，不是注入事实已证明的证书。

可用于三种有限目的：

- 在小示例中引入背景假设；
- 翻译或实验时标明精确证明债务；
- 暂时陈述日后应成为已检查 `claim`、`thm`、内置规则或源码局部引用结果的定理/库事实。

代价明确：`trust` 引入假命题后，后续结果可能继承。严肃数学发展须让剩余 trust 可见，视为假设或证明债务，不是完整证明。Litex 报告信任边界，严格模式拒绝已执行用户 `trust`、`trust have` 和 `axiom`，包括嵌套证明与导入依赖。纯 `abstract_prop` 签名和命名基础规则释放仍允许，两者都不提供任意用户假设事实。

<a id="why-does-litex-infer-extra-facts-after-accepting-a-line"></a>

## 为什么接受一行后还推导额外事实？

某些事实带常规后果，Litex 存储它们，避免用户手写每个投影、成员、定义域事实或构造式条件。

例如知道函数对象与合法输入后，可使用定义域与返回集信息。记录某些集合或笛卡尔积事实后，可推导基本成员与投影。结构成员有意不同：一般 `e $in &Struct` 不存元组、字段或规律后果；只由直接 `e &Struct` 符号绑定，或显式经成员检查的 `release struct def e` 释放。

这让证明接近普通数学文字。

例如 `have x R*` 后 `have square R = x^2` 会记录 `square $in R+`。相关事实是非零实数平方为正，不需证明 x 自身为正。幂推导先复用现有检查规则，零与 `i^2` 不能使用。

用户一次陈述有意义的结构事实，检查器记录人通常记在心里的小后果。

标量消去也是例子：

```litex
forall a, b, k R:
    k != 0
    a * k = b * k
    =>:
        a = b
```

存储乘积相等会用已有非零证书发布剩余等式；和无需非零条件消去直接公共加数。`a-k=b-k`、`k-a=k-b` 也发布 `a=b`。除法 `a/k=b/k` 要求 `k!=0`，`k/a=k/b` 还要求商 WD 条件 `a!=0`、`b!=0`。公共零分子不提供分母相等。不同于加/乘，减/除不消去 `a-k=k-b` 或 `a/k=k/b` 等交叉位置。

候选来自两操作数树，不搜索全部涉及 `a`、`b` 的事实。域与非零检查最多使用调用者权限下的 KnownSpecialProperty，不展开、重结合或匹配别名。`k!=0` 后来才出现时，须重述乘积相等触发推导。缺非零证书或零因子绝不消去。见[消去示例](../examples/infer/equal/nonzero_factor_cancellation.lit)。引用该新推导的 Lean 编译仍不支持，会安全拒绝而不引入假设。

例如 `n $in N` 时，`closed_range(0, n) $subset N` 直接成立；`{k closed_range(0, n): P(k)}` 只过滤有限基础，因而有限。若再证明非空，可使用其有限最小值及继承的自然数载体。

<a id="why-does-obtain-name-witnesses-explicitly-and-can-its-source-be-a-prop"></a>

## 为什么 `obtain` 显式命名见证？来源可以是 prop 吗？

存在事实说某对象存在，后续常需为其选名称并使用性质。`obtain ... from exist` 就是普通数学动作。

例如：

```litex
witness exist u R st {u > 0, u < 1} from 1 / 2:
    1 / 2 > 0
    1 / 2 < 1
obtain w from exist v R st {v > 0, v < 1}
w > 0
```

第一块证明存在，`obtain` 为匹配存在陈述引入见证名 `w`，随后见证性质在上下文可用。

命名定理唯一直接结论是肯定 `exist` 或 `exist!` 时，先 `release thm` 存存在，再从该 exist `obtain`；或在 `claim` 内保留存在并按需命名见证：

```litex
have q Q
release thm rational_has_unique_reduced_fraction(q)
obtain p, d from exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}
```

（`obtain … from thm …` 已移除；推荐两步形式。）

多结论、非存在或否定存在结论、名称数量不匹配均被拒绝。

具体 prop 可作为存在的命名包装：

```litex
prop has_copy(a R):
    exist x R st {x = a}

$has_copy(2)
obtain copy from $has_copy(2)
copy = 2
```

同一包装也可作为 `witness` 目标：

```litex
prop divides(p Z, u Z):
    exist k Z st {p = u * k}

witness $divides(6, 2) from 3:
    6 = 2 * 3
```

主要证明事实是 `$divides(6, 2)`，不是解析器展开的存在。执行时检查活动定义恰有一条肯定普通 `exist`，实例化并复用普通见证检查器。正常定义推导随后提供匹配存在。唯一存在应写显式 `witness exist! ...`，包含唯一性义务，再用 `by def` 单独引入命名谓词。

这是有意的窄接口。先验证来源 prop，再复查保留的定义并代入调用参数。定义必须恰有一条肯定普通 `exist`；`exist!` 定义、抽象 prop、否定来源、`not exist` 或额外条款都不被此命名见证形式接受。

存在陈述是事实；`obtain` 名称表示选定见证及其已检查类型和主体事实。这些是运行时契约。早期 Lean 实验描述用 `Exists.choose` 与 `choose_spec` 重放的可能性，但后端不属于当前构建，本节不声称当前 Lean 可重放。

<a id="how-do-function-ranges-and-preimages-work"></a>

## 函数值域与原像如何工作？

`fn_range(f)` 是函数 `f` 到达的值集。已知某值在值域中时，数学上可选原像，`have by fn_preimage` 将其变为显式证明步骤。

例如：

```litex
sketch:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    have by fn_preimage: x from f(1) $in fn_range(f)

    x $in R
    x > 0
    f(1) = f(x)
```

多参数函数每个参数提供一个原像名称。功能虽小但重要：把“值在值域中，取映到它的点”变为可检查、命名的动作，而非隐式跳跃。

<a id="what-is-strategy-for"></a>

## `strategy` 用来做什么？

用于困难在被检查对象内部结构、而非外围谓词名的证明模式。普通 `forall` 匹配按形状检索存储结论并作结构参数代换。支持的构造器可沿嵌套项递降，固定子项使用已有 Direct 相等证据；不搜索无关子表达式或额外 foralls 来创造代换，那样昂贵且难审计。

谓词还用作实际 WD 接口时尤其重要。假设 `f`、`g`、`h`、`t` 已知可微或可积，库知道该性质对逐点加、减、乘封闭。嵌套匿名函数如：

```text
fn(x R) R {f(x) + (g(x) - h(x)) * t(x)}
```

没有 strategy，用户可能须手写中间块：先 `g - h`，再 `(g - h) * t`，最后与 `f` 求和。数学常规，但语法深。

`strategy` 将结构论证打包为一个已检查命名全称证明。深推理位于定义体；定义成功后，匹配的非相等原子目标可经专门已知策略搜索应用（匹配/实例化机制同已知 forall，但按策略名引用）。策略不注入普通已知 forall 匹配。

形状如下：

```text
strategy name:
    ? forall parameters:
        assumptions
        =>:
            $target_predicate(...)
```

定义后，遇到匹配谓词目标可使用策略。可见性遵循普通环境与词法作用域。严肃文件中的策略应有真实检查证明，或清楚标注证明债务，同其他可复用全称事实一样。

<a id="why-can-definition-folding-stay-fast-in-a-large-context"></a>

## 为什么大上下文中的定义折叠仍可快速进行？

具体命题的普通折叠和显式 `by def` 知道须证明的精确条款，因此先检查直接存储参数载体与精确缓存条款，只有有界路线未建立要求时才开启更宽搜索。这不绕过定义：缺全称或存在条款仍使折叠失败。

同一有界原则用于内置最大成员规则。它只证明有限非空 `N` 子集的标准最大值存在形状；移除有限或非空性，目标仍未知。

<a id="why-did-an-inline-forall-or-an-old-builtin-theorem-call-fail"></a>

### 行内 forall 或旧内置定理调用为什么失败？

`forall x R: x > 0 => x > 0` 现在将前提与箭头分开解析。定理内 `by induc n` 选择已有目标绑定变量 `n`，不重新声明。同名嵌套声明仍被拒绝。25 个旧命名内置定理调用现在有原生 `release thm`
契约。失败 JSON 指明定理、阶段与失败前提。例如 `subset_of_finite_set_is_finite({2}, {1})` 在 `{2} $subset {1}` 失败。

<a id="how-does-calculation-treat-the-imaginary-unit-and-empty-indices"></a>

### 计算怎样处理虚数单位与空索引？

计算使用保留字面量 `i² = -1`，所以 `i*i = -1` 和 `(1+i)*(1-i) = 2` 无需额外改写可检查。符号分母消去仍需非零前提。索引并、交和笛卡尔积在 WD 时要求索引非空；命名空族函数不会启用空索引恒等式。

<a id="do-enumeration-nested-proof-methods-and-eval-check-the-same-boundaries"></a>

### 枚举、嵌套证明方法与 eval 检查同样边界吗？

有限枚举检查每个条件实例，只跳过已证明为假的原子前提；其他情况下在局部前提下证明结论。量化名称对嵌套证明仍可用。定义域必须是显式有限列表集或具体整数区间，不支持 `cart(...)` 枚举。`by` 证明体经与 claim/witness 主体相同的检查事务入口运行嵌套语句，只发布外围目标。嵌套模板不能用 `trust have` 绕过 `-strict`。`eval` 在改写或执行算法之前检查源码表达式 WD；成功计算发布当前作用域的已检查 `source = result` 等式。计算或检查失败不发布等式。

[有限集证明示例](../examples/stmt_nodes/by/finite_set_conditional_proof_steps.lit)与 [eval 定义域示例](../examples/stmt_nodes/command/eval_source_domain.lit)展示边界。真前提下假结论、域外调用是语句测试集中的可执行拒绝对照。

<a id="can-a-proved-constant-unique-existence-source-be-renamed"></a>

### 已证明的常量唯一存在来源能重命名吗？

能。证明 `forall t R: exist! y R st {y = 0}` 后，`have fn f by exist!` 可要求用 `x`、`z` 命名的同一陈述。验证器重放整个已证明命题，再查 WD，记录来源 FactId 与绑定名称重命名。未使用的 `t` 不被赋任意值。载体、前提、唯一性与自由定义所有者仍须匹配；局部 `value` 不能替换 `Other::facts::value`。

[常量来源示例](../examples/stmt_nodes/definition/forall_source_replay.lit)包含完整检查证明。测试也拒绝未证明来源、普通 `exist` 来源和删除前提的来源。[嵌套函数来源示例](../examples/proof_nodes/forall/known_exist_nested_function_alpha.lit)还检查存在函数载体内部的绑定变量重命名。定义域、返回载体、保护条件与自由身份必须相同。[嵌套唯一来源示例](../examples/proof_nodes/forall/known_source_nested_unique.lit)还重复具有嵌套全称前提、依赖闭区间 `exist!` 见证的已证明 forall。这是结构性源码复用，仍按当前权限查 WD，拒绝改变唯一性、任一映射条件或完整输入域。

<a id="can-decimal-aliases-complex-reciprocals-and-finite-aggregates-be-checked-directly"></a>

### 小数别名、复数倒数与有限聚合能直接检查吗？

能。小数字面量精确规范化，`2.400 = 2.4` 成功，`2.400 != 2.4` 被拒绝。专门内置规则以任一方向证明 `i != 0`，带保护复数计算检查 `1 / i = -i`。`1 / i = -1` 和除以 `i - i` 被拒绝。

数值/聚合修正将模块缓存兼容版本升至 ABI 3，后续接口修正升至 ABI 4。旧导入产物重建一次，因为缓存定理接口省略证明体，不能保留先前错误接受。布局不变，独立数值解码也规范化旧拼写。

有限 `sum`、`product` 实例化每个索引，检查函数域并折叠精确值。命名函数、嵌套聚合、精确分数与显式有限集使用同一路线。一次求值的全部嵌套聚合共享 1024 项额度；整数端点算术被检查。一般有限集做数值 eval 需已知枚举。符号常量、线性、逐点、分割和平移恒等式使用各自已检查前提，不枚举未知端点。来源和目标区间合法性可能需显式假设。

`eval` 显示结果，在当前作用域发布已检查 `source = result`。算法调用引用定义方程；失败不发布结果。后续断言可用 FactId。Detailed 保留代换、每项、运行总和与存储结果。见 [eval 发布示例](../examples/stmt_nodes/command/eval_store_result.lit)、[数值示例](../examples/proof_nodes/equal/by_builtin_rule/numeric_normalization.lit)、[复数示例](../examples/proof_nodes/equal/by_builtin_rule/imaginary_division.lit)、[聚合计算示例](../examples/proof_nodes/equal/by_builtin_rule/aggregate_calculation.lit)与[符号恒等式](../examples/proof_nodes/equal/by_builtin_rule/aggregate_identities.lit)。

<a id="can-negative-powers-fraction-comparisons-and-periodic-trig-values-be-checked-directly"></a>

### 负幂、分数比较与周期三角值能直接检查吗？

能。`2^(-3)=1/8`、`1/3<1/2`、`min(1/3,1/2)=1/3` 使用精确计算。非零底数与分母要求仍被检查；零的负幂或除零被拒绝。有理数回退用有界已检查整数，拒绝溢出，不做近似。

```litex
have k Z
tan(pi + 2 * k * pi) = 0
sin(pi / 6 + 2 * k * pi) = 1 / 2
C_abs(3 - 4 * i) = 5
C_abs(-4 * i + 3) = 5
```

周期规则查整数成员关系，仅 `have k R` 不够。正切与余切极点仍无定义。数值复数模接受两种加数顺序与符号，计算精确坐标并选非负根。`eval C_abs(1+i)` 显示 `sqrt(2)`，存储 `C_abs(1+i)=sqrt(2)`。Detailed 记录周期整数证据或模的坐标及平方值。见[周期示例](../examples/proof_nodes/equal/by_builtin_rule/periodic_trig_exact_values.lit)与[模示例](../examples/proof_nodes/equal/by_builtin_rule/numeric_complex_modulus.lit)。

<a id="can-tangent-and-cotangent-quotient-identities-verify-directly"></a>

### 正切和余切的商恒等式能直接验证吗？

以下两项固定恒等式在部分操作条件下可验证：

```litex
forall x R:
    sin(x)!=0
    cos(x)!=0
    =>:
        tan(x)*cot(x)=1

forall x R:
    cos(x)!=0
    =>:
        1+tan(x)^2=1/cos(x)^2
```

支持反向等式或交换乘积/和顺序；平方也可写成重复乘法。移除非零条件、使用极点或换角仍拒绝。固定规律不提供一般三角展开程序。见[乘积示例](../examples/proof_nodes/equal/by_builtin_rule/tan_cot_product.lit)与[平方示例](../examples/proof_nodes/equal/by_builtin_rule/tan_square_reciprocal_cosine.lit)。

<a id="can-equivalent-written-principal-bounds-be-used-directly"></a>

### 等价书写的主值界能直接使用吗？

固定反函数、正弦序与非零区间消费者识别四种字面下端点：`(-pi)/2`、`-(pi/2)`、`0-pi/2`、`(-1)*(pi/2)`，支持两个比较方向：

```litex
forall y R:
    -(pi/2)<=y
    y<=pi/2
    =>:
        arcsin(sin(y))=y
```

实际条件与引用保留在证明中。正切与余弦非零仍要求开区间；更宽或缺失界仍被拒绝。见[验收示例](../examples/proof_nodes/equal/by_builtin_rule/arcsin_principal_bound_spellings.lit)。

<a id="how-does-a-negative-multiplier-affect-inequalities"></a>

### 负乘数怎样影响不等式？

负公共因子反转严格序，非正因子（含零）反转弱序。因子可在每个乘积任一侧：

```litex
forall a,b,c R:
    0>c
    a>b
    =>:
        c*a<b*c

forall a,b,c R:
    c<=0
    a<=b
    =>:
        a*c>=c*b
```

实际符号证明与反向参数比较都保留。弱/零前提不支持严格结论，缺符号或参数序仍拒绝。规则继承调用者前提权限，不在受限阶段打开定义或改写。[严格](../examples/proof_nodes/atomic/by_builtin_rule/negative_common_factor_order.lit)与[弱](../examples/proof_nodes/atomic/by_builtin_rule/nonpositive_common_factor_weak_order.lit)示例记录支持的归档 overlay 检查；当前共享启动编译仍是独立待完成检查。

<a id="do-first-quadrant-bounds-suffice-for-tangent-and-cotangent-wd"></a>

### 第一象限界足以支持正切和余切 WD 吗？

足够。实际严格界在检查部分操作前认证正弦与余弦非零。固定正性规则使用相同书写界：

```litex
forall x R:
    0<x
    x<pi/2
    =>:
        0<tan(x)

forall x R:
    x>0
    pi/2>x
    =>:
        cot(x)>0
```

每条规则保留两条实际界引用。闭界、缺界、错误符号与极点仍拒绝。见[象限示例](../examples/proof_nodes/atomic/by_builtin_rule/trig_first_quadrant.lit)与[商 WD 消费者](../examples/proof_nodes/equal/by_builtin_rule/trig_first_quadrant_quotient_wd.lit)。

<a id="why-should-stored-whole-numeric-values-precede-their-arguments"></a>

### 为什么应先使用存储的完整数值，再处理其参数？

同时有 `a=0`、`cos(a)=1` 时，先替换参数可能隐藏完整余弦等式。数值代换先匹配原完整项，再访问子节点并检查重建的父项，使结果不依赖数值表行顺序：

```litex
claim:
    ? forall a,b R:
        a=0
        b=pi
        =>:
            cos(b)<cos(a)
    cos(a)=cos(0)=1
    cos(b)=cos(pi)=-1
    cos(b)<cos(a)
```

引用所选等式，消耗现有改写权限后验证改写比较。[示例](../examples/proof_nodes/atomic/by_builtin_rewrite/closed_numeric_subterm_priority.lit)与针对性测试也覆盖相等和 `eval` 消费者。

<a id="can-stored-function-values-shorten-an-algebraic-equality"></a>

### 存储的函数值能缩短代数等式吗？

能。相等改写 `KnownFnValueSubstitution` 可复用直接存储的值，不写展开后的中间表达式：

```litex
have fn shift(x R) R = x + 3
thm affine_value_product:
    ? forall x R:
        2 * shift(x) = 2 * x + 6
    shift(x) = x + 3
```

函数值等式仍须显式提供。路线在原标量树的一次遍历中替换两侧符合条件的调用，记录来源方程，关闭改写且不允许一般定义/forall 展开后检查残余。新插入的调用不再次展开。若一个调用有多个不同的直接值，应给显式中间表达式。WD、局部作用域与部分操作保护仍必需。[示例](../examples/proof_nodes/equal/by_builtin_rewrite/known_fn_value_substitution.lit)也覆盖坐标计算。

<a id="can-rational-exponents-compute-exact-rational-values"></a>

### 有理指数能计算精确有理数值吗？

能，对于闭合正有理底数，且精确根存在于经过检查的 `i128` 算术范围内：

```litex
8^(1/3)=2
16^(3/4)=8
(1/27)^(-1/3)=3
eval (4/9)^(1/2)
```

使用中央闭合计算与 `eval` 相同的精确求值器。约分指数 `p/q` 要求约分底数的分子分母有精确 q 次根，再做整数幂。无理结果不四舍五入：`let u=2^(1/3)` 良定义，但 `eval 2^(1/3)` 拒绝。精确求值器的非整数幂仍要求正底数；独立 WD 域也允许零的正实指数。见[有理幂示例](../examples/proof_nodes/equal/by_builtin_rule/closed_rational_power_calculation.lit)。

<a id="can-a-symbolic-positive-real-base-have-a-real-exponent"></a>

### 符号正实底数能取实指数吗？

能。幂 WD 现在接受正实底数与任意实指数，或非负实底数与正实指数：

```litex
forall a R+, t R:
    a^t $in R
forall x R:
    exp(x) = e^x
```

自然数幂保留 `0^0=1`。零的负幂、负底数的非整数幂和一般复指数被拒绝。符号表达式良定义不意味着能精确计算或全部恒等式可证。见[幂 WD 示例](../examples/wd/pow_real_domains.lit)。

<a id="are-fraction-rounding-numeric-radicals-complex-parts-and-rational-logs-calculations-or-rules"></a>

### 分数取整、数值根式、复数分量与有理对数属于计算还是规则？

闭合表达式使用纯计算叶。例如：

```litex
floor(-7 / 3) = -3
sqrt(12) + sqrt(27) = 5 * sqrt(3)
img((1 + 2 * i) / (3 - i)) = 7 / 10
log(8, 4) = 2 / 3
eval log(1 / 3, 27)
```

同样精确算术提供 `eval` 结果与发布等式。符号规律保留已有带前提内置规则或策略。计算前查全部输入域。平方根保留非负主值，数值对数使用精确素数指数比。不支持根式求逆、因式分解额度耗尽或算术溢出时，拒绝计算。小数近似不证明相等。四个闭合计算示例（已停用历史任务记录）及配对可执行负例记录边界。

<a id="why-can-a-strict-positive-lower-bound-make-a-logarithm-goal-well-defined"></a>

### 为什么严格正下界能让对数目标良定义？

存储 `1 < x` 现在发布 `0 < x`：严格来源与闭合证明 `0 <= 1` 论证前向后果。更一般 `b < x` 可在同受限推导阶段使用可用 `0 <= b`。[严格界示例](../examples/infer/atomic/strict_lower_bound_positive.lit)保留原对数前提。这不让负或未知界推出正性，也不扩展 WD 搜索权限。

已存储的 R 返回函数在应用域检查后，可在已知性质阶段提供 `f(a) $in C`，这是数值载体包含。检查器要求每个候选存储返回签名都符合目标。函数空间成员还要求完整输入域：定义在 `union(S,{a})` 的函数不能发布为 `fn(x S) R` 成员。应构造 `have fn restricted(x S) R = f(x)`，以该值用于较小域。有限乘积插入仍要求新鲜性前提。原生模板/字段签名保留已检查产生者。

<a id="which-real-trigonometric-interval-facts-can-be-checked-directly"></a>

### 哪些实数三角区间事实能直接检查？

检查器对通常区间有固定符号与单调性规则。以下独立片段显式保留正切分母 WD，并使用原角度界：

```litex
forall x R:
    0<x
    x<pi/2
    =>:
        0<sin(x)
        0<cos(x)

forall a,b R:
    -pi/2<a
    b<pi/2
    a<b
    cos(a)!=0
    cos(b)!=0
    =>:
        tan(a)<tan(b)
```

余弦在 `[0,pi]` 反序，正切在 `(-pi/2,pi/2)` 保序，余切在 `(0,pi)` 反序，正弦在 `[-pi/2,pi/2]` 保持弱序与严格序。固定端点拼写和反向条件引用实际书写事实。选定下界、上界和参数序结果在 Detailed 可见。这些是有界区间检查，先查部分操作 WD。弱参数界不能支持严格像不等式，极点仍无效。见[区间示例](../examples/proof_nodes/atomic/by_builtin_rule/trig_interval_monotonicity.lit)。
