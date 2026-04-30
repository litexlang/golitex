# Litex Builtin Semantics

Litex 的 builtin 不是一堆零散的 shortcut。它们共同组成了语言的“内置语义层”。

这个语义层做三件事：

1. 定义哪些数学对象是语言的基本概念。
2. 定义这些基本概念之间有哪些默认关系。
3. 定义 verifier 可以自动使用哪些机械化证明方法。

每个概念本身通常很简单，每个关系也通常很简单；复杂性来自组合数量很多。例如：函数、集合、相等、属于、序列、矩阵、order、整数区间，这些概念两两组合后会产生大量基础事实。Litex 把这些基础关系内置起来，让用户可以把注意力放在真正想证明的数学内容上。

## 1. Builtin Concepts

Builtin concepts 是语言认为足够基础，所以直接作为 keyword、object shape、fact shape 或 statement shape 存在的概念。

它们不是用户用 `prop` 定义出来的概念，而是 parser、runtime、verifier 都认识的核心对象。

### 1.1 Sets and Standard Sets

| name | category | meaning |
|---|---|---|
| `set` | parameter type | 任意集合 |
| `nonempty_set` | parameter type | 非空集合 |
| `finite_set` | parameter type | 有限集合 |
| `N` | standard set | 自然数，包含 `0` |
| `N_pos` | standard set | 正自然数 |
| `Z` | standard set | 整数 |
| `Q` | standard set | 有理数 |
| `R` | standard set | 实数 |
| `R_pos` / `R_neg` / `R_nz` | standard set | 正实数、负实数、非零实数 |

这些集合不只是名字。比如 `n N` 会给 verifier 提供 `n >= 0` 这样的基础语义；`x R_pos` 会提供 `0 < x` 这样的基础语义。

### 1.2 Function Spaces

`fn` 是 Litex 表达函数空间的基本对象构造器。

```litex
fn(x S: P(x)) T
```

表示一类函数：输入参数 `x` 来自 `S`，满足可选 domain 条件 `P(x)`，返回值属于 `T`。

这个概念连接了：

1. 参数集合
2. domain 条件
3. 返回集合
4. 函数对象的 membership
5. 函数调用的 well-definedness

例如：

```litex
f $in fn(x R: x > 0) R
```

表示 `f` 是一个能接收正实数输入并返回实数的函数对象。

### 1.3 Sequence and Matrix Concepts

`seq`、`finite_seq`、`matrix` 是常用数学对象，但在 Litex 内部它们和 `fn` 空间有直接关系。

```litex
seq(s) = fn(x N_pos) s

finite_seq(s, n) = fn(x N_pos: x <= n) s

matrix(s, m, n) = fn(x, y N_pos: x <= m, y <= n) s
```

这些关系说明：

1. 序列是从正自然数到 `s` 的函数。
2. 长度为 `n` 的有限序列是定义域限制为 `x <= n` 的函数。
3. `m` by `n` 的矩阵是两个正自然数坐标到 `s` 的函数。

因此这类对象不需要额外的 `by seq`、`by finite_seq`、`by matrix` 语句。它们可以直接通过 builtin facts 和普通事实验证来使用。

### 1.4 Logical Concepts

| name | category | meaning |
|---|---|---|
| `forall` | logical fact constructor | 建立参数、domain facts、then facts 之间的全称关系 |
| `forall!` | inline forall | 单行形式的 `forall`，用于局部或简写语法 |
| `exist` | logical fact constructor | 引入 witness，使 body facts 成立 |
| `exist!` | logical fact constructor | 唯一存在 |
| `prop` | user-defined concept | 用已有概念定义新谓词 |
| `abstract_prop` | abstract concept | 只声明谓词名字和参数，不给定义 |

`forall` 和 `prop` 是用户扩展语言概念的主要方式。Builtin concepts 是语言自带的；用户新定义的概念则通过 `prop` 和 `forall` 接入同一个证明系统。

## 2. Builtin Semantic Bridges

Builtin semantic bridges 是基本概念之间的内置关系。它们回答的问题是：一个概念怎样转化、约束、推出另一个概念？

### 2.1 Membership: Object and Set

```litex
x $in S
```

`$in` 连接对象和集合。

它是 Litex 里最核心的关系之一，因为很多“类型信息”本质上都是 membership：

```litex
x R
```

可以理解为：

```litex
x $in R
```

不同形状的集合会触发不同的语义。例如：

| set shape | semantic effect |
|---|---|
| `R_pos` | infer / verify `0 < x` |
| `N` | infer / verify `x >= 0` |
| `range(a, b)` | infer `x $in Z`, `a <= x`, `x < b` |
| `closed_range(a, b)` | infer `x $in Z`, `a <= x`, `x <= b` |
| `{a, b}` | infer `x = a or x = b` |
| `fn(...)` | register function-space information |

### 2.2 Equality: Object and Object

```litex
a = b
```

`=` 连接两个对象，表示它们相同。

在 Litex 中，`=` 同时承担几种基础角色：

1. 普通数学相等。
2. calculation 的目标。
3. known fact matching 的核心。
4. 代数变形的桥梁。
5. 对象定义和函数定义的结果。

例如：

```litex
0 = a - b
```

可以 infer：

```litex
a = b
```

### 2.3 Function Equality

`$fn_eq` 和 `$fn_eq_in` 是函数相等的语义桥。

```litex
$fn_eq_in(f, g, S)
```

表示 `f` 和 `g` 在集合 `S` 上逐点相等。

```litex
$fn_eq(f, g)
```

表示两个函数在共享定义域上相等，并且 verifier 会同时关心它们的函数空间归属。

这类 builtin 的意义是：用户不需要每次手写完整的逐点 `forall`。Litex 可以把函数相等关系转成适合 verifier 处理的 pointwise equality。

### 2.4 Implication and Equivalence

```litex
A => B
```

建立 domain facts 到 then facts 的蕴含关系。

```litex
A <=> B
```

建立双向可用的等价关系。

在 `forall` 中，`=>` 把条件和结论分开：

```litex
forall x R:
    x > 0
    =>:
        x * x > 0
```

这表示：对所有 `x R`，如果 `x > 0`，那么 `x * x > 0`。

## 3. Builtin Verification Mechanisms

Builtin verification mechanisms 是 verifier 自动使用的机械化证明方法。它们不是新的数学对象，而是“如何证明”的内置过程。

### 3.1 Calculation

Calculation 处理可计算表达式的相等关系。

```litex
1 + 2 = 3
```

这类事实不需要用户提供证明过程。Litex 会直接计算两边并比较结果。

### 3.2 Known Fact Matching

如果一个事实已经被存储，新的相同事实可以直接验证。

```litex
know a = b

a = b
```

第二行可以由已知事实验证。

### 3.3 Forall Instantiation

已知 `forall` 可以推出特例。

```litex
know forall x R:
    x = x

1 = 1
```

核心机制是匹配和替换：

1. 把目标事实和 `forall` 的 then facts 匹配。
2. 解出 forall 参数应该替换成什么对象。
3. 检查参数类型和 domain facts。
4. 得到目标事实。

### 3.4 Order Algebra

Order algebra 连接 arithmetic symbols 和 order symbols。

处理的符号包括：

```litex
+ - * / < <= > >=
```

例子：

```litex
a <= b
0 <= c
```

可以帮助验证：

```litex
a + c <= b + c
```

这类规则在数学上基础、重复、机械，所以适合内置。

Absolute value 的比较语义也属于这一类 order rule。Litex 可以直接验证：

```litex
x <= abs(x)
-x <= abs(x)
abs(x + y) <= abs(x) + abs(y)
abs(x - y) <= abs(x) + abs(y)
x ^ 2 = abs(x) ^ 2
```

这些规则把 `abs` 和 `<=`、偶数次方连接起来，表达绝对值作为大小上界、距离度量，以及“偶数次方忽略符号”的基础语义。

### 3.5 Number in Standard Set

Litex 可以直接判断字面数或可计算数是否属于标准数集。

例如：

```litex
1 $in N_pos
0 $in N
-1 $in Z
```

这些属于基本数系语义。

### 3.6 Function Membership

当已知：

```litex
f $in fn(x S: P(x)) T
```

Litex 会记录 `f` 的函数空间信息。之后验证函数调用时，可以使用这些信息检查：

1. 输入参数是否满足 `S`
2. 输入参数是否满足 domain condition `P(x)`
3. 返回值是否属于 `T`

### 3.7 Set Membership Expansion

某些集合 membership 会展开成更基础的事实。

例如：

```litex
x $in {1, 2}
```

可以 infer：

```litex
x = 1 or x = 2
```

又比如：

```litex
x $in closed_range(a, b)
```

可以 infer：

```litex
x $in Z
a <= x
x <= b
```

### 3.8 Structural Evaluation

Litex 对 list、tuple、matrix 等结构对象有内置求值规则。

例如：

```litex
[[1, 0], [0, 1]] ++ [[1, 0], [0, 1]]
```

可以 eval 到：

```litex
[[2, 0], [0, 2]]
```

这类规则建立的是“结构对象”和“逐元素运算”之间的关系。

## 4. Entry Format

后续每个 builtin entry 可以按这个格式记录：

```text
### name

类别：
    Builtin Concept / Builtin Semantic Bridge / Builtin Verification Mechanism

连接的概念：
    A
    B

语法：
    ...

数学意思：
    ...

builtin 作用：
    ...

典型例子：
    ...

相关代码：
    ...
```

例如：

```text
### finite_seq

类别：
    Builtin Concept + Builtin Semantic Bridge

连接的概念：
    finite_seq(s, n)
    fn(x N_pos: x <= n) s

语法：
    finite_seq(s, n)

数学意思：
    长度为 n、元素来自 s 的有限序列。

builtin 作用：
    Litex 内置 finite_seq 和对应 fn space 的等价关系。

典型例子：
    finite_seq(R, 3) = fn(x N_pos: x <= 3) R

相关代码：
    src/builtin_code/common_facts.rs
```

## 5. First Batch To Document

第一批可以先整理这些：

1. `set`, `nonempty_set`, `finite_set`
2. `N`, `N_pos`, `Z`, `Q`, `R`, `R_pos`, `R_nz`
3. `$in`
4. `=`
5. `<`, `<=`, `>`, `>=`
6. `fn`
7. `$fn_eq`, `$fn_eq_in`
8. `seq`, `finite_seq`, `matrix`
9. `range`, `closed_range`
10. `forall`, `exist`, `prop`

这些覆盖了最核心的“对象、关系、验证机制”。结构稳定后，再把 `docs/builtin_verify_rules.md` 和 `docs/builtin_inference_rules.md` 里的机制按这个格式搬进来。
