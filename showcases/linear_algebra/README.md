# 用 Litex 构建线性代数

这份课程讲稿参考 Sheldon Axler 的《Linear Algebra Done Right》（LADR）的主要概念，展示怎样从具体运算逐步构建一个可检查的线性代数体系。正文采用自己的教学顺序，围绕实数平面展开，适合希望了解数学概念如何写成 Litex 代码的读者。

从 [linear_algebra.lit](linear_algebra.lit) 顺序阅读即可。动机、计算、定义、构造和证明穿插在同一个文件中：先看两个坐标怎样运算，再构造域与向量空间，接着寻找子空间，最后用方向列表描述整个平面。

## 从坐标到空间

向量直接使用原生有限序列；列表的长度已经在类型中，取元素直接调用序列：

```litex
have e1 finite_seq(R, 2) = (1, 0)
have e2 finite_seq(R, 2) = (0, 1)
have standard_basis finite_seq(finite_seq(R, 2), 2) = (e1, e2)

standard_basis(1) = (1, 0)
standard_basis(2) = (0, 1)
```

这几行摘自正文的两个位置。相同接口也能表示重复方向和空列表，无需额外定义 `FiniteList`。

`Field` 携带标量运算和域公理，`VectorSpace` 携带向量运算和空间公理。讲稿实际构造了 `real_field` 与 `real_plane`，逐项验证它们满足公理，再从这些公理证明零元和逆元的唯一性。子空间则是已有子集的性质；两个坐标轴满足它，平移直线给出反例。

## 从方向到基

线性组合把系数与同长度的向量列表配对。`span` 是这些组合构成的实际集合，正文中的定义为：

```litex
template<K nonempty_set, field &Field<K>, V nonempty_set, space &VectorSpace<K, field, V>, n N, vectors finite_seq(V, n)>:
    have span power_set(V) = {x V: $is_linear_combination(K, field, V, space, n, x, vectors)}
```

这段代码使用正文中此前定义的域、空间和线性组合关系。随后证明：两个标准方向张成整个平面，并且线性无关，因此构成基；重复同一个方向则不独立。最后证明每个向量的标准坐标唯一，回到开头的坐标表示。

## 阅读地图

| 正文位置 | 数学内容 |
|---|---|
| 第一章 1.1–1.3 | 原生序列、坐标运算、实数域、向量空间、公理验证与零元/逆元唯一性 |
| 第一章 1.4–1.5 | 函数的点运算、坐标轴子空间、平移直线反例、轴分解及其唯一性 |
| 第二章 2.1–2.2 | 有限线性组合、两项求和、span、标准方向张成平面 |
| 第二章 2.3–2.4 | 线性无关、重复方向反例、基、标准展开与坐标唯一性 |
| 第二章 2.5 | 有限维、长度为 2 的基、一般维数定义的动机 |

本版用 Litex **1.0.6-beta** 严格验证了全部 **86 条顶层语句**，源码没有 `trust`、`axiom` 或 `abstract_prop`。它是连贯的两章课程示例，不代表覆盖 LADR 前两章的全部内容。

一般长度的线性组合关系已定义，求和构造目前验证到两项。一般基的删减与扩张、基长度不变及 `dimension` 的定义留待后续；函数空间目前展示点运算，没有完成全部空间公理。

[math_collections.md](math_collections.md) 解释概念的依赖与接口选择。[litex.config](litex.config) 将本模块导出为 `linear_algebra`。命令行用法见仓库的 [CLI 文档](../../docs/cli.md)。
