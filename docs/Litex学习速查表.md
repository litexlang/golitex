<a id="litex-learner-cheatsheet"></a>

# Litex 学习速查表

用本页选择下一条声明、证明步骤或修复方式。Litex 按源码顺序检查语句；已接受的对象和事实成为后续语句的上下文。以下每个可运行代码块都是自足的。

安装见[安装指南](安装Litex.md)。[手册](Litex手册.md)负责精确的语言契约；[CLI](Litex命令行参考.md)负责命令与输出。

> **Litex 适合与 AI 交互：提出事实、检查、读取反馈，在同一个活动 `-session` 中修正或继续。普通失败保留此前已接受的定义和事实。绝不要每加几条新代码就从头重跑。** 见[简单对照](#run-and-read-feedback)。

<a id="find-your-next-move"></a>

## 找到下一步

| 我需要…… | 从这里开始 |
| --- | --- |
| 引入值、函数或条件 | [选择语句](#choose-a-statement) |
| 陈述假设与结论 | [书写事实与假设](#write-facts-and-hypotheses) |
| 定义对象并证明其规律 | [定义 → 定理 → 使用](#definition--theorem--use) |
| 给出或提取见证 | [存在性与作用域](#existence-and-scope) |
| 选择证明方法 | [证明动作](#proof-actions) |
| 理解失败语句 | [常见卡点](#common-places-to-get-stuck) |
| 查询数集、索引或结构 | [对象与定义域](#objects-and-domains) |
| 运行文件并查看结果 | [运行并阅读反馈](#run-and-read-feedback) |

<a id="the-working-model"></a>

## 工作模型

```litex
have x R = 2
x + 1 = 3
x^2 = 4
```

`have` 引入实数对象及其值。后续每条事实都会被检查；成功后可供下一条语句使用。

| 类别 | 示例 | 作用 |
| --- | --- | --- |
| 对象 | `x`、`R`、`{1, 2}`、`x + 1` | 数学值或表达式。 |
| 事实 | `x = 2`、`x $in R`、`$P(x)` | 关于对象的命题。 |
| 语句 | `have`、`prop`、裸事实、`claim` | 引入、定义或检查信息。 |
| 反馈 | `statement_result`、`proof_method`、`stores`、`why_failed` | 解释结果与可用上下文。 |

写一行之前，识别它的对象、定义域以及接下来需要的精确事实。声明新数学概念之前，先查看已有内置和模块接口。

<a id="choose-a-statement"></a>

## 选择语句

以下形式是示意；`S`、`T`、`value` 和 `goal` 代表你的实际对象与事实。

| 后续代码需要 | 形式 | 提供什么 |
| --- | --- | --- |
| 任意成员 | `have x S` | 名称与成员关系；要求非空性。 |
| 带声明载体的值 | `have x S = value` | 检查 `value $in S`；记录成员关系和相等。 |
| 表达式名称 | `let name = value` | 相等别名，不是可变赋值。 |
| 可调用值 | `have fn f(x S) T = body` | 带定义域、输出载体和方程的函数。 |
| 命名数学条件 | `prop P(x S): facts` | 定义；用 `$P(a)` 断言实例。 |
| 局部推导 | `claim: ? goal` | 证明并导出目标；辅助内容留在局部。 |
| 命名的可复用结果 | `thm name: ? goal` | 证明事实并提供引用接口。 |

条件和值有不同用途。以下定义通过检查定义体建立特定实例：

```litex
prop is_above_two(t R):
    t > 2
by def $is_above_two(3)
```

仅声明 `prop` 不证明任何实例。`abstract_prop` 只提供签名。如果下一行需要 `f(x)`，应定义可调用函数，而不是把该值编码成谓词。见 [R02](Litex手册.md#r02-choose-the-language-form-by-mathematical-role)。

<a id="write-facts-and-hypotheses"></a>

## 书写事实与假设

| 数学形状 | 形式 |
| --- | --- |
| 相等、序、成员关系 | `a = b`、`a <= b`、`a $in S` |
| 命名性质 | `$P(a)` |
| 相邻事实链 | `a = b = c`、`a <= b < c` |
| 合取或可选情况 | `$P(a) and $Q(a)`、`$P(a) or $Q(a)` |
| 存在 / 唯一存在 | `exist x S st {facts}`、`exist! x S st {facts}` |
| 全称结果 | `forall x S:`，后接缩进事实 |

条件全称陈述中，假设放在 `=>:` 前，结论放在其后：

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

没有箭头时，列出的事实全部是结论。无前提的全称陈述直接列结论。`forall` 绑定变量和前提属于局部，不引入全局对象或全局假设。

裸 `forall` 的主体包含事实。`witness`、`by def` 和 `release thm` 等命令属于证明体。全称结论参数使用一个头部；嵌套量词前查阅[事实契约](Litex手册.md#factual-statements)。平坦的 `and`/`or` 形式不是任意布尔语法。

实数距离计算中，直接陈述对称性和三角不等式：

```litex
forall x,y,z R:
    |x-y| = |y-x|
    |x-z| <= |x-y|+|y-z|
```

两个坐标误差界也能约束两个最小值或最大值之差。若 `a,b R+` 已检查，要选共同正半径，可写 `have delta R+ = min(a,b)`。自足示例与固定前提边界见[距离与极值预览](Litex手册.md#r10-expose-absolute-value-bounds)。

<a id="definition--theorem--use"></a>

## 定义 → 定理 → 使用

倒数的非零条件属于可调用定义域。命名定理使用当前活动的目标绑定变量，并暴露定义等式：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
thm reciprocal_product:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1

release thm reciprocal_product(2)
reciprocal(2) * 4 = (reciprocal(2) * 2) * 2 = 1 * 2 = 2
```

依次阅读为定义域契约、已证明全称规律、显式实例与后续计算。定理中的 `x` 是局部变量，可直接在证明体内使用。每次定理调用仍检查参数与前提。

| 引用 | 效果 |
| --- | --- |
| `release thm name(args)` | 实例化根 `forall` 定理，发布全部结论。 |
| `by thm name(args) => fact` | 选择直接返回的一条原子结论，不改写它。 |
| `release thm name` | 引用命名的非 `forall` 定理事实。 |

零参数的根 `forall` 仍使用 `name()`。选择目标不能是链、合取、存在或全称事实；应释放结果，再用显式后续步骤。避免重复已发布的结论，除非该步骤进行了必要的表示变换。

见 [R01](Litex手册.md#r01-define-and-use-a-reciprocal-function)、[P05](Litex手册.md#p05-a-function-equation-may-need-to-be-exposed-before-substitution) 和[定理调用契约](Litex手册.md#theorem-fact-shapes-and-call-spelling)。

<a id="existence-and-scope"></a>

## 存在性与作用域

证明存在性时，给出满足条件的见证。使用能够验证的存在事实时，通过 `obtain` 提取一个新名称：

```litex
witness exist w R st {w^2 = 4} from 2
obtain root from exist w R st {w^2 = 4}
root^2 = 4
```

`obtain` 检查来源，不能凭空创造未证明的见证。绑定变量 `w` 属于存在陈述的局部。新名称 `root` 属于外围作用域。若见证需要实际的中间推理，再加入见证证明体。

“对每个 `x` 都存在 `y`”中，应在活动的 `x` 作用域内选择见证。claim 激活目标绑定变量，并导出完成的目标：

```litex
claim:
    ? forall x R:
        exist y R st {y = x + 1}
    witness exist y R st {y = x + 1} from x + 1
```

claim 不导出全局的 `x` 或 `y`。唯一存在还要求唯一性：`2` 是 `w^2 = 4` 的见证，但 `-2` 也是。确实唯一的规格可以直接检查：

```litex
witness exist! w R st {w = 2} from 2
```

见[见证](Litex手册.md#s35-existential-witnesses)、[唯一见证](Litex手册.md#s36-unique-existential-witnesses) 和[局部 claim](Litex手册.md#s33-local-claims)。

<a id="6-small-proofs-write-the-route-only-when-needed"></a>

<a id="proof-actions"></a>

## 证明动作

普通验证能建立目标时，先直接陈述目标。如果证明需要显式数学动作，选择对应命令。以下条目是缩略形式，不是完整可运行程序。

标量消去时，直接陈述剩余等式：

```litex
forall a, b, k R:
    k != 0
    a * k = b * k
    =>:
        a = b
```

`a+k=b+k` 也会发布 `a=b`，且无需非零条件。公共操作数必须直接出现在两侧。减法支持 `a-k=b-k` 与 `k-a=k-b`。除法支持带 `k!=0` 的 `a/k=b/k`，以及带 `k!=0`、`a!=0`、`b!=0` 的 `k/a=k/b`。减法/除法要求操作数位置匹配；`0/a=0/b` 不能消去分子。非零证书应放在乘积等式之前；若证书后来才出现，应重新陈述等式。展开、重结合和别名匹配不属于该推导规则。见[消去契约](Litex手册.md#equality-and-structural-inference)。

| 所需动作 | 命令 | 契约/示例 |
| --- | --- | --- |
| 使用肯定形式的具体定义 | `by def $P(args)` | [S47](Litex手册.md#s47-explicit-definition-folding) |
| 引用命名结果 | `release thm` / 带选择的 `by thm` | [S25–S26](Litex手册.md#s25-publish-theorem-conclusions) |
| 提供 / 提取见证 | `witness` / `obtain` | [存在性](#existence-and-scope) |
| 在穷尽分支中证明共同结果 | `by cases:` | [S39](Litex手册.md#s39-proof-by-exhaustive-cases) |
| 从分类后的相反命题导出矛盾 | `by contra:`，以 `impossible` 结束 | [S40](Litex手册.md#s40-proof-by-contradiction) |
| 检查显式有限集 | `by enumerate finite_set:` | [S41](Litex手册.md#s41-finite-set-enumeration) |
| 遍历具体整数区间 | `by for:` | [S44](Litex手册.md#s44-finite-range-iteration) |
| 证明自然数不变式 | `by induc n from lower:` | [S42](Litex手册.md#s42-ordinary-induction) |
| 使用此前全部归纳情况 | `by strong_induc n from lower:` | [S43](Litex手册.md#s43-strong-induction) |
| 证明集合 / 函数相等 | `by extension` / `by fn_extension` | [S45–S46](Litex手册.md#s45-set-extensionality) |

有限枚举检查每个允许的赋值及其局部前提：

```litex
by enumerate finite_set:
    ? forall x {1, 2}:
        x > 0
    x > 0
```

归纳提供基础情况与后继步骤。归纳假设只在步骤中可用；证明辅助内容留在各自情况内：

```litex
claim:
    ? forall n N:
        2^n >= n + 1
    by induc n from 0:
        ? 2^n >= n + 1
        ? from n = 0:
            2^n = 1 = n + 1
        ? induc:
            2^(n + 1) = 2^n * 2^1 = 2^n * 2
            2^n * 2 >= (n + 1) * 2
            (n + 1) * 2 = (n + 1) + (n + 1) >= (n + 1) + 1
            2^(n + 1) = 2^n * 2 >= (n + 1) * 2 >= (n + 1) + 1
```

<a id="common-places-to-get-stuck"></a>

## 常见卡点

修改证明前，先阅读最早停止的阶段。以下被拒绝的块是有意的边界示例，不参加正向测试。

<a id="an-arbitrary-member-has-no-chosen-value"></a>

### 任意成员没有选定值

**预期搜索失败（`search_proof`）：**

<!-- litex:skip-test -->
```litex
have x R
x = 0
```

声明建立实数成员关系，不建立 `x = 0` 或 `x != 0`。如果想要的对象是零，应显式引入该值：

```litex
have x R = 0
x + 1 = 1
```

<a id="an-expression-must-be-meaningful-on-its-whole-domain"></a>

### 表达式必须在整个定义域内有意义

**预期函数体失败（`have_fn_equal`）：**

<!-- litex:skip-test -->
```litex
have fn reciprocal(x R) R = 1 / x
```

该定义域包含零。部分倒数应使用[上面的保护定义](#definition--theorem--use)。若函数在零处也有值，需要在定义中指定它。参数载体和索引边界同样受检查；修复时保留原本的数学定义域。

<a id="a-fact-list-cannot-execute-a-proof-command"></a>

### 事实列表不能执行证明命令

**预期解析错误：**

<!-- litex:skip-test -->
```litex
forall x R:
    witness exist y R st {y = x + 1} from x + 1
```

使用 [claim 形式](#existence-and-scope)，其证明体可以在目标绑定变量活动时执行命令。

| 后续代码停止的情形 | 下一步检查 |
| --- | --- |
| 函数应用 WD 失败 | 精确输入载体和保护条件；已知值等式不能免除它们。 |
| 较大等式搜索失败 | 暴露改变的子项或定义等式，再连接外围表达式。 |
| `$P(a)` 未证明 | 建立定义中的各项条件；声明 `prop` 只提供词汇。 |
| `exist!` 失败 | 同时检查唯一性和见证主体。 |
| 名称在证明后消失 | 导出的是目标，而不是局部绑定变量和辅助内容。 |
| 定理选择失败 | 结构性匹配返回的原子结论；另行改写。 |

已检查的拒绝与最近修复见[陷阱卡片](Litex手册.md#pitfalls-and-missing-proof-steps)。搜索失败不反驳事实，也不能单独证明内核有错误。`trust` 假定事实，会留下证明债务，而不是修复验证路线。

<a id="objects-and-domains"></a>

## 对象与定义域

| 对象类别 | 常用形式与边界 |
| --- | --- |
| 数集 | `N`、`Z`、`Q`、`R`、`C`；`N` 包含零，`N+` 是正数。 |
| 带符号/非零集合 | 例如 `R+`、`R-`、`R*`、`C*`；使用文档列明的拼写。 |
| 集合 | `{1, 2}`、`{x R: x > 0}`、`union(A, B)`、`power_set(S)`；集合构造式受其载体约束。 |
| 成员关系与包含 | `x $in S`、`A $subset B`；包含与相等的义务不同。 |
| 函数 | `fn(x R) R`、带保护的定义域、`fn_range(f)`；载体与保护条件约束每次调用。 |
| 原像 | `preimage(f, y)` 收集输出等于对象 `y` 的输入；`preimage_set(f, Y)` 收集输出属于 `Y` 的输入。两者返回集合，并保留完整输入定义域与保护条件。[预览契约](Litex手册.md#preview-point-and-set-preimages)。 |
| 元组/序列 | `(a, b)`、`cart(R, R)`、`finite_seq(S,n)`、`seq(S)`；索引从 1 开始。`release tuple def t` 发布精确的有限序列成员关系和坐标；`release cart def cart(A,B)` 发布完整集合定义。见 [S52](Litex手册.md#s52-release-a-tuple-definition)。 |
| 精确计算 | `eval expression` 检查定义域，发布已验证的源码/结果等式。 |

函数参数载体与返回载体使用外围作用域；不能引用该签名自己的参数。保护条件和函数体可以引用。例如 `fn(x R: x > 0) R {x + 1}` 的定义域依赖保护条件。不要从普通 `forall` 绑定变量的依赖推断任意依赖函数签名。见 [S01](Litex手册.md#s01-expression-defined-functions)。

数学结构需要成为带字段的值时，可使用 struct：

```litex
struct Point:
    x R
    y R
have p &Point = (1, 2)
release struct def p
p.x = p(1) = 1
p.y = p(2) = 2
```

精确构造和规律契约见[结构](Litex手册.md#s16-structured-carriers)与[模板](Litex手册.md#s17-parameterized-declaration-families)。已有内置概念无需局部重定义。

<a id="supported-syntax-and-recommended-writing"></a>

## 支持的语法与推荐写法

| 支持的拼写 | 新的普通示例的推荐写法 |
| --- | --- |
| 裸 `by thm name(args)` | 无选择的调用使用 `release thm name(args)`。 |
| 行内 `forall x R: x > 0 => x != 0` | 使用多行 `forall`，让假设与结论清晰可见。 |
| 文档列明的 Unicode 别名 | 使用 ASCII 关键字与操作符，便于输入、搜索和诊断。 |

这些是偏好，不是解析器限制。选择仍使用 `by thm ... => fact`。`×` 表示笛卡尔积；数值乘法用 `*`。`⊂` 是真子集，`⊆` 是非严格子集。见[别名参考](Litex手册.md#unicode-mathematical-input-aliases-preview)。

普通数学示例优先使用 `|x|`；`abs(x)` 仍被支持。竖线包围完整表达式，`|x|^2` 表示 `abs(x)^2`。嵌套的 `||x||` 表示 `abs(abs(x))`；复数模、范数与基数没有竖线重载。乘法仍须显式书写（`2 * |x|`），诊断保留 `abs(...)`。

```litex
|-3| = abs(-3) = 3
forall x, y R:
    |x + y| <= |x| + |y|
```

平方的相反数写 `-(x^2)`；负值的平方写 `(-x)^2`；负指数写 `x^(-1)`。义务已经能验证时，优先使用直接的 `by def $P(args)` 和无证明体见证。实际推导或必要桥接所需的中间事实应保留。

<a id="run-and-read-feedback"></a>

## 运行并阅读反馈

```bash
litex -lang en -e '1 + 1 = 2'
litex -lang en -strict -f path/to/file.lit
litex -lang en -strict -r path/to/project
```

源码检出版本中，用 `cargo build --release` 构建并使用 `target/release/litex`。`-f` 挂载直接父目录中存在的 `litex.config`，运行配置中直到该文件的前缀；否则独立运行文件。`-r` 检查完整的已配置项目。

书写迭代时，用 `litex -session -f path/to/file.lit` 一次加载已通过前缀，并在同一个 REPL 中继续；也可以先接受一个值：

```bash
litex -lang en -session -e 'have a R = 2'
```

每次分别提交一条语句；每一轮都输出 Normal run JSON（`target: "repl"`）。软失败 JSON 在这里被缩略：

```text
litex> a = 3
{"run_result": "failure", "target": "repl", "errors": [{"phase": "...", "category": "...", ...}], "session_terminated": false, "termination": null}
litex> a + 1 = 3
{"run_result": "success", "target": "repl", "statement_results": [...], "errors": [], "session_terminated": false, "termination": null}
```

失败语句之后，`a = 2` 仍然可用。作为对照，分别运行 `litex -e 'have a R = 2'` 和 `litex -e 'a + 1 = 3'` 不能共享声明，第二条会失败。不要每做一个小改动就重新加载此前所有已接受语句。缩进的 REPL 块用空行结束。在连贯的阶段检查点和最终 JSON 检查时，另行运行批量命令。进程停止或上下文必须改变时，重启并重放已接受源码；见 [Agent Guide](Litex智能体指南.md)。

机器读取时使用 `-lang en`。要求退出码为 0，且批量封装具有以下字段（省略其他字段）：

```json
{
  "kind": "run",
  "run_result": "success",
  "session_terminated": false, "termination": null
}
```

| 结果 | 下一步 |
| --- | --- |
| 成功 | 判断可复用内容时，查看 `proof_method`、`stores` 和 `infers`。 |
| 语句 `statement_result: "rejected"` | 阅读 `why_failed.phase` 和 `why_failed.goal`；失败语句不新增成功事实。先前已接受语句仍可使用。 |
| `session_terminated: true` | 阅读结构化 `termination`；当前运行/会话已停止。 |

软失败语句会让整体批量运行失败，即使后续语句成功。不要从嵌套证据文本推断成功，也不要把失败断言当成其否定。见 [CLI 结果](Litex命令行参考.md#statement-outcomes)。

`-strict` 拒绝执行的用户 `trust`、`trust have` 和 `axiom`，包括依赖中的内容。抽象谓词签名和命名基础规则的释放仍被允许。验证仍依赖检查器、内置/推导规则和已加载数学；应准确报告显式假设与未解决的证明债务。见[信任契约](Litex手册.md#trust-and-strict-mode)。

较大数学发展应遵循相关模块的 `README.md` 和 `math_collections.md`，再查阅[示例](../examples/README.md)与[数学展示](../showcases/math_concepts_in_litex/README.md)。
