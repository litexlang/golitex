# Chapter 2 与原书的对应关系

第二章正文现在按原书的 2.1–2.5 排列。第一道题就是实数上的
`a * b * c = b * (a * c)`，使用 `a, b, c R` 与内置乘法。
原书到 2.2 才引入一般 Ring、CommRing、AddGroup、Group；这里也如此。
此前直接以任意 `add` 和一长串公理开篇的做法，是迁移时过度泛化造成的偏离。

源版本：`6dfa2c166a410d2f0f278d327ea81ae0fa6d3c32`，
`MIL/C02_Basics/S01_Calculating.lean` 至
`S05_Proving_Facts_about_Algebraic_Structures.lean`。

| 原书小节 | 正文内容与对应示例 |
| --- | --- |
| 2.1 Calculating | 实数乘法的交换、结合与重排；两个假设下的乘积替换；四因子替换；`c = b*a-d, d=a*b` 推出 `c=0`；平方和展开、两个和的乘积、平方差；`c=d*a+b, b=a*d` 推出 `c=2*a*d`；最后保留原书自然数上的平方计算。 |
| 2.2 Algebraic Structures | Ring 的九类原始等式；CommRing 上的乘法重排、平方和、平方差与假设替换；MyRing 的零元、逆元、消去、乘零、负负、减法、自减与二倍；AddGroup 的三条检查；Group 的三条检查和右逆、右单位元、乘积逆元。 |
| 2.3 Using Theorems and Lemmas | 实数的弱/严格传递与五点混合链；线性估计；exp/ln 单调性和 exp 的 iff；加法单调、严格单调、正性；指数和与正对数参数；平方非负、减指数、`2ab ≤ a²+b²` 和绝对值乘积估计。 |
| 2.4 Order and Divisibility | 实数 min 的投影与最大下界性质、min/max 交换、min 结合、平移估计与等式、绝对值三角与反三角；自然数整除的传递、乘积、平方、混合和；gcd/lcm 的零规律与总定义 gcd 对称性。 |
| 2.5 Algebraic Structures | PartialOrder 的弱序、严格序、混合传递与严格序 iff；Lattice 的上下界性质、交换、结合、吸收；四种分配律及两个条件分配律的互推；有序环的减法非负两方向与非负右乘；度量的自距、对称、三角和由三角不等式推导的非负性。 |

正文每个证明前的 `S01:`–`S05:` 注释进一步标出原书的对应数学项。
同一命题的多种 `rw`、`calc`、`ring`、`apply` 等 Lean 写法合并；不同命题不合并。
原书留作练习或 `sorry` 的数学项也保留并给出 Litex 证明。
未单独展开类型的 `#check abs_le'.mpr`，在最后的绝对值乘积证明中对应“两侧界推出绝对值界”的分情况步骤。
这次对齐数学内容、具体/抽象对象和小节顺序，不声称逐行复现 Lean 的 tactic 教学。

## 对应接口与必要的差异

- 实数示例使用内置 `R`、算术、`exp`、`ln`、`min`、`max`、`abs`。
  正对数参数的证明保留在本地；没有把原书的实数变量偷偷缩到 `R+`。
- 一般 Ring/Group 使用带运算和规律的结构对象。CommRing 是现有 Ring 上的
  `is_commutative_ring`。AddGroup 单独使用 `AdditiveGroup`，不额外假设交换律。
  为证明平方差，本地先给出负元乘法的派生引理；它在 2.2 内的落点晚于原书
  使用 Mathlib 现成引理的位置，这是显式的本地依赖调整。
- `nat_divides(divisor N, dividend N)` 使用自然数见证，包含零除数。
  内置 `$dvd` 的顺序是被除数、除数，而且要求除数非零，因此不能直接覆盖原书的总关系。
- `natural_gcd(m, n N)` 在 `m=0` 时返回 `n`，其余情况使用内置 `gcd`。
  因而包含 `natural_gcd(0,0)=0`，并证明任意自然数对的对称性。
  原书的 lcm 零规律可直接使用内置 `lcm`，包括两参数均为零。
- PartialOrder 是满足三条规律的关系；Lattice 携带该关系及 meet/join。
  `is_strict_ordered_ring` 记录本节使用的加法、非负乘法、严格正乘法兼容规律；
  它不是对 Mathlib 整个 typeclass 层级的重新实现。本节三个有序环证明实际上
  只需其中的弱兼容规律，因此使用较少假设的 `is_ordered_ring`。
- `SourceMetricSpace` 用零距分离、自距为零、对称和三角不等式刻画距离函数。
  `source_metric_distance_nonnegative` 从三角不等式推导 `0 ≤ 2*dist(x,y)` 再除以 2；
  没有把非负性预先作为该结果的假设。

## 兼容附录

`Compatibility appendix` 位于五节正文之后。旧的显式 `add`/`mul` 参数定理、
构造规律、整数见证 `divides`、非零对的旧 `gcd_comm`、旧 `MetricSpace` 接口等
仍在那里，供后续章节已有调用使用。旧接口名称和数学签名保留；正文不再从它们开篇。
旧 `MetricSpace` 将非负性列为条件，正文则使用上述可推导非负性的接口。

验证范围和可执行文件/章节哈希见 [verification.json](verification.json)。
