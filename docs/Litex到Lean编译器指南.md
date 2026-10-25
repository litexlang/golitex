<a id="litex-to-lean-compiler-guide"></a>

# Litex 到 Lean 编译器指南

本指南通过具体的源码与生成结果示例，解释 Litex 到 Lean 编译的设计原则。它是持续维护的阅读入口，说明编译器为什么这样工作，以及输出意味着什么。

想直接查看已经完成的工作，可以沿着下面的[例子阅读路径](#explore-the-example-collection)，
再浏览[完整的源码／生成结果集合](../lean/examples/)。

[编译器 README](../src/compile_to_lean/README.md)解释从 Runtime 到原生接口的架构、
带类型结果的所有权、Core 语义及原生接口边界。本指南讲面向用户的设计原则和详细用法；
完整示例分别放在自己的 README。[CLI 文档](Litex命令行参考.md#lean-compiler-boundary)负责命令行契约。

<a id="from-a-checked-fact-to-a-lean-proof"></a>

## 从已检查的事实到 Lean 证明

最小的例子是[一等于自身](../lean/examples/one_equals_itself/statement.lit)：

```litex
1 = 1
```

它的[生成 Lean 文件](../lean/examples/one_equals_itself/statement.lean)包含以下声明。这里逐字保留声明，省略外围命名空间：

```lean
theorem h_1 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
```

`Litex.number` 表示源码中的数；`Litex.Same` 通过对象的含义表达源码相等。证明使用 `Litex.sameRefl`，因为成功的 Litex 结果记录了相同的两个端点。这明确了编译器的核心任务：重放 Litex 实际检查的证明路线。

分别运行独立源码、查看编译器输出：

```sh
target/release/litex -strict -lang en -f lean/examples/one_equals_itself/statement.lit
target/release/litex -strict -lean -f lean/examples/one_equals_itself/statement.lit
```

第二条命令将 Lean 源码写到标准输出。生成源码和用 Lean 内核检查源码是两个不同步骤。

<a id="explore-the-example-collection"></a>

## 从几十组实际例子开始

[证明语句对应与验收](Litex_To_Lean_Proof_Commands.md)按主题列出复合反证、集合／函数外延、强归纳、有限枚举和中点几何的源码／生成 Lean 对，并说明各适配器当前支持的范围。

最短的源码／生成证明／Adapter／Final 完整讲解见
[加零示例 README](examples/litex_to_lean/add_zero/README.md)。
[Newton README](examples/litex_to_lean/newton_residual/README.md)进一步展示
函数的非零定义域条件如何保留到编译结果和原生接口中。

[完整例子集合](../lean/examples/)中，每组 Litex `.lit` 源码都配有编译器生成的 `.lean` 文件。
2026-10-12 的验收检查了 74 对，包含严格源码验证、实际编译、重新生成的一致性，
以及固定版本的 Lean/Mathlib 检查。例子集合仍在这一验收节点之后继续增长；
下面列出当前集合的阅读起点，可以逐行同时打开源码和生成证明：

| 数学步骤 | Litex 源码 | 生成的 Lean | 重点看什么 |
|---|---|---|---|
| 精确分数与小数 | [源码](../lean/examples/exact_fractions_and_decimals/statement.lit) | [Lean](../lean/examples/exact_fractions_and_decimals/statement.lean) | 精确计算，以及 `1 / 3` 与 `0.333` 的区别。 |
| 带定义域条件的倒数 | [源码](../lean/examples/guarded_real_reciprocal/statement.lit) | [Lean](../lean/examples/guarded_real_reciprocal/statement.lean) | 函数定义、在二处求值，以及保留下来的非零前提。 |
| 闭单位区间 | [源码](../lean/examples/closed_unit_interval/statement.lit) | [Lean](../lean/examples/closed_unit_interval/statement.lean) | 有界集合构造、成员关系，以及每个成员满足的上下界。 |
| 复用定理的多个结论 | [源码](../lean/examples/named_compound_theorem_returns/statement.lit) | [Lean](../lean/examples/named_compound_theorem_returns/statement.lean) | 多项返回事实，以及后续证明如何明确选择所需结论。 |
| 两个有理互逆函数 | [源码](../lean/examples/rational_inverse_maps/statement.lit) | [Lean](../lean/examples/rational_inverse_maps/statement.lean) | 同一段数学开发中的定义、定义域保持、两条互逆律和单射性。 |

逐组比较源码中的数学陈述与中间事实，以及生成定理的前提和证明引用。
这些例子把编译器的开发工作留成了可以检查的具体产物，覆盖算术、对象构造、定义与证明复用。
[验收说明](#what-successful-output-establishes)解释注明日期的检查及其范围；后面的有理函数讲解
还会沿着最后一组例子走到普通 Mathlib 接口。

<a id="compile-the-evidence-behind-the-fact"></a>

## 编译事实背后的证据

成功的源码运行不只包含最终命题，还记录所选验证路线、对象良定义性证据、子证明和对先前事实的引用。编译按源码顺序消费这些带类型的结果。

Rust 入口明确区分执行阶段与编译阶段：

```rust
let result = runtime.run_litex_code(&source)?;
let compiler = LitexToLeanCompiler::new(runtime);
let lean = compiler.compile_run(&result, &artifact_namespace)?;
```

编译器取得 Runtime 的所有权，并通过方法参数接收已完成的结果，然后分派既有的 `ExecStmtResult` 及其带类型的子枚举。Runtime 被移动而不克隆；编译器只有这一个字段，没有生命周期参数。它的文件结构对应执行器的语句与验证分支。每个分支读取原始主体和选定证据，编译子节点，生成临时 Lean 表达式。它不维护第二套对象、事实、定理或参数模型。

借用的源码位置游标识别原始结果的祖先节点和已完成的阶段前缀。这样既保留先前引用与局部边界，也不必复制 ExecEnv 或维护独立证明注册表。来源 ID 将每个源码证明声明和引用命名为 `h_<original FactId>`，包括参数、保护条件、推导事实和命名定理。语句位置决定执行顺序，不用于分配证明名称。参数签名来自声明的原始位置，因此后来的 `have` 不能扩展先前定理的输入。

对象构造器可能依赖局部成员关系证明或非零证明。如果导出的命题使用该证明名，生成类型会将所需的实际证明表达式作为局部 `let` 值包含进去。这使 Lean 表达式闭合，而不把已证明事实变成新的定理假设。

Runtime 执行源码一次，然后移动到编译器中，作为只读的精确 ID 解析器。销毁 Runtime 后，当前结果并不自足：某些源码阶段保留的是 ID，而非完整的产生者载荷。只有整个产物成功时，`compile_run` 才返回源码。该方法可以接收另一个结果，而不保留先前输出。自由函数 `compile_run` 委托同一实现，现在也按值接收 Runtime。

对于 `1 = 1`，记录的路线是自反性。对于 `a + 0 = a` 这样的事实，所选有理式规范化路线必须经过对应的规范化适配器。识别最终等式并改用无关的加零定理，会丢失与源码证明的联系。所选适配器内的固定规范化可以消解数值证书；这不授权无限制的目标证明搜索。

这一区分也规定了支持边界：命题可以在 Litex 中验证通过，但其具体证据路线可能不在当前编译器的支持范围内。编译接受该路线之前，必须为它提供明确的适配器。

<a id="formula-functions-and-concrete-predicates"></a>

## 有限集合与有界 builder

[有限自然数集合](../lean/examples/finite_natural_set/statement.lit)保留源码元素及其两两不等证明：

```litex
have small_naturals set = {1, 2}
1 $in small_naturals
small_naturals $subset N
```

生成表示逐项使用认证的 `Litex.insert` 对象，每个元素保持原来的 host 表示。
`{1, 1}` 和 `{1 + 1, 2}` 仍按源码 WD 规则被拒绝。枚举顺序属于构造顺序，
集合的数学相等由成员决定。

[非负有理数集合包含关系](../lean/examples/nonnegative_rational_subset/statement.lit)使用有界分离：

```litex
have nonnegative_rationals set = {x Q: x >= 0}
have nonnegative_reals set = {x R: x >= 0}
nonnegative_rationals $subset nonnegative_reals
```

`Litex.setBuilder` 保留认证的界集，并对认证的成员解释筛选条件。
谓词 WD 只证明表达式合法，不证明所有元素都满足它。条件按源码顺序保留证明：
在 `{x R: x != 0, 1 / x > 0}` 中，前面的非零证明认证后面的除法。
空界集不需要选择元素；空域全称证明先消费记录的空集等式，再消去矛盾。

`SetSemantics M` 的规律由实际 ZF 模型证明，函数域共用其中的分离操作。
`have A set` 与 `forall A set` 保持 generic host 表示；`set` 不表示一个万能集合。
原生数值集合视图只观察相应的数值成员。若要把它解释为整个集合，还必须有
`A $subset R` 或 `A $subset C` 的证明。原生消费者在证明体中固定已检查的模型，
对外只给出普通 ZFSet、Set Complex 与 Set Real 陈述。

当前切片支持平坦原子筛选条件、平坦 And／数值比较链及已支持的具体谓词，
按实际记录的成员、subset、binder 与有序 WD 子证明重放。有限集合保留完整的
两两不等证据；成员可经实际 subset 证明用于实数序的 WD。
一般析取筛选、finite_set 参数、独立的 `have A nonempty_set`、无界理解、幂集／像与存在式集合选择
仍在编译边界外，不会被变成公理。

## 字段互不依赖的结构

```litex
struct CoordinatePair:
    x R
    y R

forall p &CoordinatePair:
    p.x = p(1)
    p.y = p(2)
```

`&CoordinatePair` 编译成已有的笛卡尔积集合封装；`p` 仍是带成员前提的通用对象。
字段名对应有限函数的坐标，`p.x` 使用这个成员证明构造 `Litex.cartCall`。
编译器按原来的 FactId 输出自动展开得到的笛卡尔积成员事实、字段等式和字段成员事实。
[完整例子](../lean/examples/coordinate_pair_fields/)还使用两个坐标做实数运算。

字段可以属于不同的集合，见[带自然数编号的点](../lean/examples/indexed_point_fields/)；
也可以使用[先前声明的任意集合](../lean/examples/arbitrary_carrier_pairs/)。
[嵌套元组成员例子](../lean/examples/nested_coordinate_membership/)先证明内层坐标对的成员关系，
再让外层结构引用它。

普通对象声明、给定值的声明和显式展开也使用同一套表示：

```litex
witness $is_nonempty_set(&CoordinatePair) from (1, 2)
have p &CoordinatePair
release struct def p
p.x $in R

have origin &CoordinatePair = (0, 0)
origin.x = 0
```

第一种声明消费 result 中的非空证明；第二种分别检查类型预检、值的 WD 和成员证明，
再输出对象别名及字段事实。展开保留原 FactId，多个参数按原顺序展开。
可以查看[任取坐标对](../lean/examples/chosen_coordinate_fields/)、
[原点](../lean/examples/origin_coordinate_fields/)、
[显式展开](../lean/examples/released_coordinate_fields/)、
[局部声明](../lean/examples/local_coordinate_objects/)、
[定理内展开](../lean/examples/coordinate_field_theorem/)和
[两个坐标对的运算](../lean/examples/coordinate_pair_addition/)。
`<=>` 条件会保留在结构的成员关系里：

```litex
struct PositivePoint:
    x R
    y R
    <=>:
        x > 0

(2, 3) $in &PositivePoint
forall p &PositivePoint:
    p.x > 0
```

生成的集合用 `Litex.setBuilder` 限制笛卡尔积。证明成员关系时，需要字段成员证明和
定义条件的证明；展开结构时，再按原 FactId 取出这些事实。[正坐标点例子](../lean/examples/positive_point_conditions/)
也检查任意笛卡尔积对象在第一坐标为正时属于这个结构。
[普通与局部声明](../lean/examples/chosen_positive_points/)和
[显式展开](../lean/examples/positive_point_release/)都保留条件。

条件按顺序检查。[正数比值](../lean/examples/positive_ratio_conditions/)先给出
`denominator != 0`，下一条 `numerator / denominator > 0` 的除法 WD 就引用它。
另有[等式](../lean/examples/equal_coordinate_conditions/)、
[合取](../lean/examples/first_quadrant_conditions/)和
[链式条件](../lean/examples/ordered_coordinate_conditions/)的生成例子。
定义发布的全称事实仍用原来的参数和 FactId；这部分复用已有集合构造定理，没有增加模型假设。

结构头参数可以定义一族集合：

```litex
struct Pair<A set>:
    x A
    y A

forall A set, p &Pair<A>:
    p.x $in A
    p.y $in A
```

`A` 仍是通用对象，`$is_set(A)` 仍是事实。生成的 Lean 定义接收这个对象和集合事实；
实例化时消费原 result 中的参数 WD 和类型证明。[通用坐标对](../lean/examples/parameterized_pairs/)
和[带等式条件的坐标对](../lean/examples/parameterized_equal_pairs/)都接受任意集合参数。
参数也可以是条件里的[实数阈值](../lean/examples/threshold_points/)，或者像
`A set, a A` 这样让后一个参数依赖前一个，见[指定第一坐标](../lean/examples/designated_coordinate_pairs/)。
[全局／局部声明和展开](../lean/examples/chosen_parameterized_pairs/)保留实例化后的字段事实。

结构头、`forall` 和命名定理也支持 `A nonempty_set`：`A` 仍是通用对象，
非空性仍是原 FactId 对应的 `Litex.IsNonempty A` 假设，不会自动选择集合里的元素。
实例化时必须提供实际的非空证明。例子包括[非空集合上的坐标对](../lean/examples/nonempty_parameterized_pairs/)、
[带等式条件的坐标对](../lean/examples/nonempty_equal_pairs/)和
[笛卡尔积非空定理及调用](../lean/examples/nonempty_cartesian_theorem/)。

后面的字段也可以依赖前面的字段：

```litex
struct RepeatedCoordinate:
    x R
    y {x}

forall p &RepeatedCoordinate:
    p.y $in {p.x}
    p.y = p.x
```

[这个例子的生成文件](../lean/examples/repeated_coordinate_fields/)用
`Litex.DependentFields` 表示按顺序依赖的字段集合，逐项重放声明时的 WD、
参数引入及其推导。`Litex.dependentCart` 收集满足这些成员条件的元组，
仍然使用原来的平坦元组表示。`p` 保留自己的通用对象表示；展开结构时，
编译器按原 FactId 输出笛卡尔积成员、字段等式和字段成员事实。

这条路线使用可选的 `IndexedUnionSemantics M`，其按集合索引的并集规律
已由现有 ZF 模型证明。只有声明依赖字段的生成文件需要这个额外接口；
`SetSemantics` 的定义不变。

更多已检查的例子包括：[集合的元素及该元素的成员](../lean/examples/member_coordinate_pairs/)
（`x A; y x`）、[三个依赖字段](../lean/examples/repeated_coordinate_triples/)、
[带正数条件的结构](../lean/examples/positive_repeated_coordinates/)、
[从已有笛卡尔积成员推出结构成员](../lean/examples/equal_coordinates_membership/)，
以及 [have、显式展开和局部别名](../lean/examples/chosen_repeated_coordinates/)。
[倒数字段](../lean/examples/reciprocal_coordinate_fields/)使用 `x R+; y {1 / x}`：
第一字段已有的非零推导为第二字段提供除法 WD，展开时引用声明已经证明的字段集合。

这一范围要求至少两个字段，字段依赖只能指向前面的字段。字段访问和展开的对象
必须是直接声明的结构参数或给定值的别名。条件限于已支持的原子事实、扁平合取
和链式事实。有限集合参数种类、量化条件、嵌套字段路径、函数调用结果和
局部／限定名的结构定义仍未接入。

## 公式函数与具体谓词

顶层 `abstract_prop` 也可以编译。例如，下面的证明把一个性质从对象传给与它相等的对象：

```litex
abstract_prop marked(x)
forall a, b R:
    a = b
    $marked(a)
    =>:
        $marked(b)
```

声明编译成谓词参数 `(abstract_prop_1 : (Fin 1 → M.Value) → Prop)`，
调用把对象的语义值传给它。证明消费原来的相等证据和性质引用；声明本身不证明任何实例。
可查看[源码与生成的证明](../lean/examples/abstract_property_transport/)、
[二元关系及其否定](../lean/examples/abstract_relation_transport/)、
[零参数命题](../lean/examples/abstract_proposition_identity/)和
[抽象性质作为函数条件](../lean/examples/abstract_function_guard/)。
局部和带模块限定名的抽象声明尚不支持。

[带保护条件的倒数](../lean/examples/guarded_real_reciprocal/statement.lit)用普通非零要求定义公式：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

生成的对象使用 `Litex.formulaFn`，求值使用 `Litex.call`。调用的 WD 包含记录的函数空间成员关系、参数成员关系及保护条件证明。对存储的源码证明的引用使用原始 `h_<FactId>` 名称。新检查的数值要求也可直接包含选定的证明表达式。`hf` 等库参数名不会重命名源码引用。

`FunctionSemantics M` 为数值接口增加图构造与求值。具体实例用 Mathlib 的 ZF 集合证明这些规律；源码函数仍是拥有自身身份的图对象。内部值函数体回调不会把源码对象替换为原生实数函数箭头。

当前公式切片支持一个或两个 N/Z/Q/R/C 输入及输出，以及已审查的 `R+` 输入和值域扩展，
还支持数值域／值域别名、先前函数的公式复合，以及直接或具体谓词保护条件。
顶层具体谓词可以使用已支持的平坦原子、And 和数值链条款。
[非负性](../lean/examples/nonnegative_real_property/statement.lit)展示谓词定义与展开；
[商的分配](../lean/examples/real_quotient_distributes/statement.lit)展示两个参数；
[带保护条件的复合商](../lean/examples/two_argument_shifted_quotient/statement.lit)展示复合调用。
编译消费每次调用实际捕获的 WD 和定义域证据。
有界的一元自然数递归图和普通零起点归纳见[编译器 README](../src/compile_to_lean/README.md)；
下文[已验证的单步 Newton 示例](#已验证的单步-newton-示例)提供完成验收的简单例子。
高阶函数体、量化谓词及该切片之外的递归仍不受支持。

<a id="definitions-and-named-theorem-citations"></a>

## 定义与命名定理引用

[命名的加零示例](../lean/examples/named_add_zero/statement.lit)结合了已证明接口、带类型的值和表达式别名：

```litex
thm add_zero:
    ? forall x R:
        x + 0 = x

have offset R = 2
let shifted = offset + 0
by thm add_zero(offset) => offset + 0 = offset
shifted = offset
```

它的[生成文件](../lean/examples/named_add_zero/statement.lean)定义了已认证的别名对象，并输出命名定理。显式调用应用先前的定理与源码参数成员关系证明，再选择实际返回的等式。最后一行沿记录的相等路线经过别名与已证明结果。编译不会用一个新的算术证明替换该调用。

源码定理的目标良定义性与证明体分别有捕获的作用域。重放两者保留实际的参数与前提产生者；局部证明定义不会变成后续的全局声明。当源码选择复用先前定理的路线时，重复的 forall 事实使用记录的该定理及绑定变量重命名。

[相等关系传递成员关系的示例](../lean/examples/equality_membership_transport/statement.lit)展示引用的另一种用途：

```litex
forall u,v C:
    u = v
    u $in R
    =>:
        v $in R
```

证明消费给定等式与实数成员关系事实。它通过指称相等传递成员关系，同时保留两个对象各自的一般宿主表示。

<a id="rational-aliases-arbitrary-numeric-contexts-and-real-order"></a>

## 有理数别名、任意数值上下文与实数序

[有理数二分之一示例](../lean/examples/typed_rational_half/statement.lit)保留字面量与拥有自身表示的除法对象之间的区别：

```litex
have half Q = 1 / 2
half + half = 1
```

它的[实际生成文件](../lean/examples/typed_rational_half/statement.lean)重放 Q 成员关系和已存储的定义等式，将记录的闭合表达式代入两个加法操作数，然后消费实际的闭合残余证明。Q 表示忠实的有理数像；成员关系从不改变别名的宿主类型。固定的证书规范化器检查记录的标量值，而不另外寻找最终目标的证明。

[任意实数示例](../lean/examples/arbitrary_real_laws/statement.lit)从一条上下文声明开始：

```litex
have arbitrary_real R
arbitrary_real + 0 = arbitrary_real
arbitrary_real >= arbitrary_real
```

编译器检查记录的非空性证明，输出一般的已认证对象和属于 R 的假设。后续定理头部保留这些参数；它不会把对象定义为零。命名证明中的局部任意 have 则在证明内部消去实际记录的非空性见证，保留原来的成员 ID 和作用域，不给导出的定理增加见证参数。[局部见证例子](../lean/examples/local_witness_additive_identity/statement.lit)同时检查局部 typed-have／let、依赖声明和 set-kind 声明。局部 prop／fn 和嵌套命名定理仍是另一个作用域扩展。

[实数平方](../lean/examples/real_squares_nonnegative/statement.lit)和[弱序传递性](../lean/examples/weak_order_transitivity/statement.lit)使用普通的 `Litex.Le`/`Litex.Lt` 事实；大于比较通过交换参数表达。其含义包含实数指称见证；任意复数对象上没有序。编译器先重放实际的 R 定义域条件，再应用选定的序定理，并保留源码前提、精确引用和偶指数限制。

[差非零示例](../lean/examples/nonzero_real_difference/statement.lit)通过原来选定的 `DiffNonzeroFromInequality` 结果编译 `x != 1 => x - 1 != 0`。精确的操作数不等子证明及数值定义域证据传给已证明的 `Litex.subNonzeroOfNotSame` 引理；同一路线也支持保持泛型表示的复数成员、零在两侧的方向，以及已认证的封闭零表达式。缺失或篡改前提证据仍会拒绝；其他非零 builtin 分支需要各自的编译支持。

[实数 Möbius 对合示例](../lean/examples/real_mobius_involution/statement.lit)接通了 `(x+1)/(x-1)` 的完整证明：在 `x != 1` 时，函数值仍不等于 1，再调用一次得到 x。编译器重放差非零、分子和分母的两个非零子证明、已知差非零的精确引用，以及原来选定的 forall 应用。非等式原子结论复用已有链式/合取消费者，保留参数匹配、类型和定义域证据；嵌套调用的定义域检查也走这条路线。等式 forall、高阶调用及其他未审查的结论分支仍有各自的支持边界。[普通 Lean 接口](../showcases/litex_to_lean_adapter/Final.lean)通过手写且已验证的 Adapter 使用生成证明。

<a id="membership-preserves-the-objects-representation"></a>

## 成员关系保留对象表示

`M : Litex.Semantics` 是携带已证明规律的数学解释：`M.Value` 是共同的语义世界，
`M.mem`、`M.isSet` 解释成员关系与集合身份，`M.number : ℂ → M.Value` 嵌入原生数值，
`M.standard` 解释 N/Z/Q/R/C。`Representation M α` 则固定 host 值如何指向这个世界，
以及哪些值满足 WD。生成定理对满足这些规律的 M 成立；原生消费者在证明体中
明确选用 `Litex.NumericModel.model`。它覆盖已检查的切片，不是全部 Litex 的完整模型。

对于一般对象，只要已有 `h : Litex.In a Litex.C`，现成的
`Litex.NativeBridge.asComplex a h : ℂ` 就给出唯一的原生复数代表；
`asComplex_spec` 证明其嵌入等于对象的 denotation。这个接口适用于任意满足契约的 M。
原对象及 α 保留；该 noncomputable 观察不将对象重新定型，也不推出任意 host 载荷相等。
`asReal` 提供相应的实数代表，两种观察的相容性及证明无关性已由 Core 证明。

[一般复数对象示例](../lean/examples/complex_object_equals_itself/statement.lit)将自反性扩展到参数：

```litex
forall a C:
    a = a
```

在它的[生成文件](../lean/examples/complex_object_equals_itself/statement.lean)中，参数仍是具有一般宿主表示的对象。下面是生成定理头部中逐字保留的片段，为便于阅读分开展示：

```lean
{_Host_i1 : Type v1}
[_rep_i1 : Litex.Representation M _Host_i1]
(_value_i1 : Litex.Obj (M := M) _Host_i1)
(h_15 : Litex.In _value_i1 (Litex.C (M := M)))
```

`a C` 提供成员关系事实，不会把对象表示替换成 Lean 的 `ℂ` 变量。定理结论是 `Litex.Same _value_i1 _value_i1`，由 `Litex.sameRefl _value_i1` 证明。

[lean/Litex.lean](../lean/Litex.lean)中的语义接口将每个对象的值与其良定义性证明打包：

```lean
structure Obj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  val : α
  wd : WD (M := M) val
```

表示独立于选用的 WD 证明，固定值的含义。数值字面量可以使用原生复数载荷；一般参数和构造表达式保留各自的表示。当所需成员关系证据可用时，已证明的桥接结果把它们的含义连接到原生数值数学。

<a id="construction-conditions-survive-compilation"></a>

## 构造条件在编译后仍然保留

[除法示例](../lean/examples/division_equals_itself/statement.lit)说明为什么证明相等要先认证对象：

```litex
forall a C, b C:
    b != 0
    =>:
        a / b = a / b
```

即使这个自反等式，也要求商良定义。[生成文件](../lean/examples/division_equals_itself/statement.lean)为两个参数引入复数成员关系证明，并引入 `b` 的非零前提。传给自反性证明的商就是以下逐字保留的生成表达式：

```lean
Litex.div _value_i1 _value_i2 h_28 h_29 h_1
```

三个证明参数分别认证两个操作数的定义域与分母非零。它们保留源码条件，而不是新增数学操作数。输出相等证明之前，编译必须建立或解析这份精确的构造证据。

<a id="citations-and-assumptions-retain-their-scopes"></a>

## 引用与假设保留各自作用域

在除法示例中，`b != 0` 属于全称定理的局部上下文。它不能成为无关的后续定理的前提。局部对象、缓存的 WD 证据和引用事实也受同样限制。

重放通过记录的 ID 识别引用，并检查其主体。缓存的构造必须解析到该对象已经重放的证据。如果 ID 缺失，或必需的推导事实没有受支持的产生者，编译会拒绝该路线。在实时环境中寻找另一条真事实，会掩盖缺失的源码依赖。

直接标量消去可以从已存储的 `a+k=b+k`、`a-k=b-k`、`k-a=k-b` 发布 `a=b`，也可以在有 `k!=0` 证书时从 `a*k=b*k` / `a/k=b/k` 发布该事实。`k/a=k/b` 还要求两个分母均非零。编译器重放当前单跳推导实际记录的消去规则、WD 和直接存储结果，再使用原始 FactId 引用。更长的消去证明须在源码里明确给出中间步骤；编译器不会自行补出第二轮 infer。原证据缺失、主体不符或引用越过已完成阶段时，仍拒绝整个产物。

<a id="what-successful-output-establishes"></a>

## 成功输出确立了什么

当前生成声明显式暴露一个语义参数：

```lean
variable {M : Litex.Semantics.{u}}
```

Lean 定理以该接口为条件。`lean/Litex.lean` 包含一个明确的候选数值模型，但尚未给出全部 Litex 对象和规则的完整解释。原生 Lean/Mathlib 消费者还需要已证明的表示桥接，必要时还需要手写适配器。该适配器是独立于编译器生成输出的产物。

验收包含三个不同部分：

1. **源码验证：** 精确的 Litex 源码成功，其选定证据得到识别。
2. **编译：** 编译器消费这些证据并生成完整产物。不受支持的语句、构造器、证明路线、引用或作用域都会导致整个产物被拒绝。
3. **生成文件与 Lean 检查：** 重新生成的结果与维护中的对应文件一致；生成证明与语义接口，在预期假设边界下通过固定版本的 Lean/Mathlib 内核检查。

不得以证明空洞或新造的公理代替不受支持的路线。`-strict` 排除源码中的 trust 和用户公理；它并不证明每项 Litex 基础都已有完整的 Lean 解释。

仅由 Litex 检查时，Rust verifier、builtin 和 infer rule 仍属于可信计算基（TCB）。
生成证明在预期公理边界下通过独立 Lean 检查后，Lean 确立的是生成定理在其显式前提下成立，
证明有效性不依赖于接受 Rust verifier 的成功报告。另一个需要审查的问题是，该定理是否忠实表达
原 Litex 陈述：对象含义、前提、构造条件和作用域仍须对应。
[Lean 的证明验证指南](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)也区分证明有效性与陈述含义。

已有编译实例为已审查的映射提供证据，并不证明所有 Rust 验证分支可靠。
读者可以从 [How Litex works](https://litexlang.com/how-litex-works)、本指南的源码／生成结果示例，
以及 [Lean 语义接口](../lean/Litex.lean)中已证明的桥接规律审查设计。这些是当前契约和假设的阅读入口。

本期原定第 8–11 阶段的最低范围在 2026-10-12 的当前单跳 typed result 上通过重新验收：74 对源码／实际生成文件、45 个维护场景，以及另记的 6 个 whole-Chain／whole-And／WD 构造实例化场景。64 个每层原生接口和普通 Lake 客户端的 64 次直接调用、6 个组合调用通过检查。当前回执是本地 scripts/litex_to_lean 中的 acceptance_phase8_current 至 acceptance_phase11_current 和 acceptance_phases8_11_current；旧回执保留为其原构建的历史证据。这些检查确立的是已审查子集及其实际选中路线。

<a id="maintaining-this-guide"></a>

<a id="using-a-generated-result-in-ordinary-mathlib"></a>

## 在普通 Mathlib 中使用生成结果

当前数学子集固定了 18 个角色：数值层级、精确有理数计算、有理数封闭性、复数代数、
实数序、相等传递性质、任意数值、别名、具体谓词、带条件公式函数、命名定理引用和
有界集合。倒数乘积例子另外检查这些角色的组合。伴随回归例子不另算新的数学角色。

以[商的分配律源码](../lean/examples/real_quotient_distributes/statement.lit)为例，
链路是源码 → 原始 typed result → 生成定理 → 手写 Adapter → 普通 Lean Final。
生成陈述保留 generic 对象、WD 和分母非零证据。Adapter 固定已检查的模型并证明
表示转换。本地 Final 对外给出普通 Mathlib 定理：

```lean
theorem realQuotientDistributes (x y z : ℝ) (hz : z ≠ 0) :
    (x + y) / z = x / z + y / z := by
  exact Adapter.realQuotientDistributes x y z hz
```

当本地 `native.Final` 模块可用时，Lean 用户可以这样引用：

```lean
import native.Final

theorem useCompiledQuotient (x y z : ℝ) (hz : z ≠ 0) :
    (x + y) / z = x / z + y / z := by
  exact NativeConsumer.realQuotientDistributes x y z hz
```

用户的定理陈述只包含实数、普通运算和非零前提。手写 Adapter/Final 属于忽略的
`scripts/litex_to_lean/native/` 本地验收工具，尚未作为自动发布的 Lean 包交付。
在另一个固定版本的 Mathlib 项目中，导入保存的生成模块和 `Litex.lean`，再为需要的
普通数学接口提供已检查的 Adapter/Final。保留生成模块的相对导入路径及其实际
命名空间。成员证明允许取得原生数值代表，同时原对象的 host 表示保持不变。

手写 Adapter 选择语义模型并证明表示转换。这些工作可在同一数学开发中复用，
后续调用者直接使用 `Adapter.realQuotientDistributes` 这样的普通定理。
新数学领域可能需要补充转换。自动生成这些 Mathlib 接口仍是后续工作。

本地选定子集的统一检查命令是：

```sh
cargo build --release
python3 scripts/litex_to_lean/check.py --subset --work-area .draft/selected-subset --profile-area .draft/selected-subset/replay-profiles
```

它记录源码与生成文件哈希、实际 typed result 的字段路径和所选规则/证书标签、
真实 Lean 检查、公理审计以及原生证明引用路径。辅助程序投影 Detailed 结果后，
直接编译同一份原始 result；JSON 只用于展示验收证据，不进入编译器。
矩阵按数学角色逐项记录。原生证明引用经过 beta/zeta 简化并沿辅助定理追踪；
未使用的局部 let 或 lambda 参数不算消费生成证明。这检查证明项中实际保留的引用，
不证明数学上的唯一必要性，也不等于形式化证明整个 Rust 翻译器的正确性。

本指南的验收数量对应固定 Lean/Mathlib 环境下、注明日期的本地检查。
语义接口、源码及其对应生成文件均公开；检查驱动和回执仍在本地工作区。
这些是本地检查记录，不是 release/tag CI 的运行结果。

任意集合有一个明确的接口差异：`$is_set(A)` 在生成端有证明，原生端的
`A : ZFSet` 则通过类型表达集合身份，无需发明额外的原生 sethood 谓词。
整个集合的数值视图仍需 subset 证据。模块、一般存在式见证证明、无界理解、
存在式集合选择、高阶函数体、有界一元自然数切片之外的递归和局部 prop／fn／嵌套 thm，
以及未审查的推理／证书路线仍在编译边界外。
在结果中观察到未被消费的 inference 节点，不代表编译器已支持该推理。

长期目标是将证明重放扩展到其余 Litex 证明路线。每项扩展都须保持源码含义、
使用结果中记录的证据，并通过 Lean 检查。

<a id="two-rational-maps-from-definitions-to-a-native-equivalence"></a>

## 两个有理函数：从定义到原生等价

[有理互逆函数源码](../lean/examples/rational_inverse_maps/statement.lit)展示一段连续的数学论证：
\(f(x)=(2x+1)/(x-1)\) 将 \(\mathbb{Q}\setminus\{1\}\) 映到
\(\mathbb{Q}\setminus\{2\}\)，其逆函数是 \(g(y)=(y+1)/(y-2)\)。
源码依次定义两个函数、证明函数值满足后续调用的定义域条件、证明两个复合恒等式，
最后通过逆函数证明单射。[生成的 Lean 文件](../lean/examples/rational_inverse_maps/statement.lean)
保留这整段论证的实际证据。

函数定义将排除值直接放进定义域：

```litex
have fn forward(x Q:x!=1) Q=(2*x+1)/(x-1)
have fn backward(y Q:y!=2) Q=(y+1)/(y-2)
```

完整源码先证明这些除法需要的基本非零事实。下面第一个定义域定理说明，
为什么随后可以合法地调用 `backward(forward(x))`：

<!-- litex:skip-test -->
```litex
thm forward_preserves_domain:
    ? forall x Q:
        x!=1
        =>:
            forward(x)!=2
    forward(x)=(2*x+1)/(x-1)
    forward(x)-2=3/(x-1)
    3/(x-1)!=0
```

`backward` 对应的定理证明其函数值不等于 1。有了两个定义域结论，源码继续证明
`backward(forward(x))=x` 和 `forward(backward(y))=y`。它们成为已证明的命名定理，
供最后的单射证明复用。在 `a!=1`、`b!=1`、`forward(a)=forward(b)` 的前提下，
证明选取这两个结果：

<!-- litex:skip-test -->
```litex
by thm backward_forward(a) => backward(forward(a))=a
by thm backward_forward(b) => backward(forward(b))=b
```

每次调用都返回选中等式、参数成员关系和定义域条件的带类型证据。编译器沿这些结果
及其原始 FactId 重放，将源码证明声明和引用命名为 `h_<FactId>`。例如，嵌套的
`Litex.call` 必须接收“内层函数值满足外层定义域”的证明；编译器解析已记录的证据，
不会将这个条件变成新的未证明假设。有理恒等式的证明同样保留原来选定的规范化路线
及其分母非零证据。

链接的生成文件中，五个导出证明使用以下源码 ID；它们均属于该文件的源码路径命名空间：

| 源码定理 | 生成声明 |
|---|---|
| `forward_preserves_domain` | `h_1042` |
| `backward_preserves_domain` | `h_5990` |
| `backward_forward` | `h_10318` |
| `forward_backward` | `h_21048` |
| `forward_injective` | `h_37256` |

公开的配套文件展示如何把结果交给 Mathlib 用户。
[RationalMaps.lean](examples/litex_to_lean/rational_inverse_maps/RationalMaps.lean)
定义普通 `ℚ` 上的两个函数。
[Adapter.lean](examples/litex_to_lean/rational_inverse_maps/Adapter.lean)
选定 `Litex.NumericModel.model`，编码有理数输入和前提，调用生成定理，再通过已证明的
函数求值与数值表示规律取得普通函数值。这个手写层证明表示之间的转换；定义域、
互逆和单射的数学结论使用生成证明。
[Final.lean](examples/litex_to_lean/rational_inverse_maps/Final.lean)
提供普通有理数定理，并把两条逆律组装成 `Equiv`：

```lean
namespace RationalMaps
def equivalence : {x : ℚ // x ≠ 1} ≃ {y : ℚ // y ≠ 2} where
  toFun x := ⟨forward x, forwardPreservesDomain x x.property⟩
  invFun y := ⟨backward y, backwardPreservesDomain y y.property⟩
  left_inv x := Subtype.ext (leftInverse x x.property)
  right_inv y := Subtype.ext (rightInverse y y.property)
end RationalMaps
```

每个 subtype 装着一个普通有理数及其不等于排除值的证明。定义域定理负责构造输出
subtype，两条逆律负责 `Equiv` 的互逆字段。用户导入 `rational_inverse_maps.Final`；
[普通 Lean 调用示例](examples/litex_to_lean/rational_inverse_maps/UseInYourProject.lean)
直接使用这个原生接口，其定理陈述无需出现 Litex 对象或语义参数。

在保留仓库目录布局的 Mathlib 项目中，可在 `lakefile.toml` 加入以下库配置。
本例检查使用 Lean 4.31.0 和 Mathlib commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。

```toml
[[lean_lib]]
name = "Litex"
srcDir = "lean"
roots = ["Litex", "examples.rational_inverse_maps.statement"]

[[lean_lib]]
name = "CompilerDocExamples"
srcDir = "docs/examples/litex_to_lean"
roots = ["rational_inverse_maps.UseInYourProject", "rational_inverse_maps.DirectLean"]
```

运行 `lake build CompilerDocExamples`，后续文件即可导入
`rational_inverse_maps.Final`。在仓库根目录用实际编译器重新生成对应文件：

```sh
target/release/litex -strict -lang en -f lean/examples/rational_inverse_maps/statement.lit
target/release/litex -strict -lean -f lean/examples/rational_inverse_maps/statement.lit > lean/examples/rational_inverse_maps/statement.lean
```

最终的单射证明显式列出非零事实并展开公式。更短的函数同余等式链可以通过 Litex
验证，却可能选中当前编译器尚未支持的路线。
[直接 Mathlib 版本](examples/litex_to_lean/rational_inverse_maps/DirectLean.lean)
展示了不经过编译和 Adapter、直接证明同一结果的写法。

## 已验证的单步 Newton 示例

[Newton README](examples/litex_to_lean/newton_residual/README.md)集中展示完整源码、
生成证明说明和普通 Lean 消费者：在 `x ≠ 0` 时，
`((x + 2/x)/2)^2 - 2 = ((x - 2/x)/2)^2`。
单步恒等式和正数更新变体的 Adapter／Final 均已检查，并消费实际生成证明。

同一 README 单独记录递归全索引实验：源码编译和字节一致的再生成完成，
完整 Lean／原生验收未完成，2026-10-13 按用户要求停止。

## 维护本指南

新增设计说明应连接到 [lean/examples/](../lean/examples/)下真实的源码/生成文件对。每个讲解都应说明数学事实、选定的源码证明路线、生成证明保留什么，以及最近的不支持边界。明确标注拟议设计与未验证示例。

以上代码片段来自维护中的示例与语义接口，不是完整的能力清单。其所属产物改变时，应同步更新。实现映射保留在[编译器 README](../src/compile_to_lean/README.md)中；开发夹具、验收记录与构建工具保留在仅限本地的编译器工作区 `scripts/litex_to_lean/`。

<a id="current-mathematical-coverage-and-examples"></a>

## 当前覆盖的数学范围与示例

`release obj def` 已支持 `let`、普通对象／集合声明、带等式的声明、从存在事实
选出的对象和公式函数。它按 result 记录的原定义找到原证明，再用新的 FactId
引用它们；局部事实仍留在原作用域。四组通过 Lean 检查的例子是
[数值与别名](../lean/examples/released_value_definitions/)、
[带非零条件的倒数函数](../lean/examples/released_reciprocal_definition/)、
[存在见证](../lean/examples/released_witness_definition/)和
[局部定义](../lean/examples/released_local_definitions/)。
模块限定名及其他定义类别尚未接入；`release tuple def`、`release cart def`
的语句与证明编译也还没有接上。

`finite_seq(A, n)` 已支持任意集合载体和自然数长度，包括零长度，定义域精确为
`closed_range(1, n)`。runtime 原本就记录了从有限序列成员到函数集合成员的推导；
编译器现在按原 FactId 输出一次，后续调用直接引用。
[有限序列集合](../lean/examples/finite_sequence_spaces/)、
[合法下标取值](../lean/examples/finite_sequence_coordinates/)和
[取第一项函数](../lean/examples/finite_sequence_first/)这三组源码／生成文件已通过 Lean 检查。
无限序列 `seq` 和 tuple/cart 定义释放仍是后续工作。

本轮新增的 Lean 检查通过例子包括：[双向全称命题](../lean/examples/equivalence_directions/)、
[关系的注册声明](../lean/examples/registered_equality/)和
[实数最小值与最大值](../lean/examples/real_min_max/)。它们覆盖局部等价命题、
任意集合对象上的谓词、三种注册声明，以及 min/max 的交换律、幂等性、实数和整数成员关系。
后续还补上了 [min/max 精确计算](../lean/examples/min_max_evaluation/)和
[上下界与单调性](../lean/examples/min_max_bounds/)，包括分数、负数、嵌套运算，
以及引用原比较前提的单调性证明。
[条件取值](../lean/examples/ordered_min_max_selection/)支持选取任意一侧及反向书写等式；
[最小值与最大值函数](../lean/examples/ordered_min_max_functions/)把 `have fn`、
函数展开、具体 `prop`、条件 `thm`、`let` 和 `by thm` 接在同一个例子中。
注册传递律之后的链式推导仍需补充编译分支。

[实数符号](../lean/examples/real_sign/)覆盖具体数值计算、整数成员关系，以及
由严格正负条件推出的等式；[平移后的符号函数](../lean/examples/shifted_sign_function/)
把它用于函数定义、嵌套调用和定理调用。底层含义通过已证明的桥接定理对应到
Mathlib 的 `Real.sign`。[乘积](../lean/examples/sign_product/)与
[取负](../lean/examples/sign_negation/)规则也已接入，包括反向等式和原 verifier 支持的取负写法。
[符号与绝对值](../lean/examples/signed_magnitude/)对任意实数证明
`sign(x) * abs(x) = x`、`abs(x) = sign(x) * x`；
[方向与大小函数](../lean/examples/direction_magnitude_functions/)把这些等式用于命名定理和函数乘积。

[向下／向上取整](../lean/examples/rounding_integers/)支持精确分数计算和整数不变性，
例如 `floor(-3 / 2) = -2`、`ceil(-3 / 2) = -1`。
[上下界与单调性](../lean/examples/rounding_bounds/)保留原实数域和比较证据，
通过已证明的桥接定理对应到 `Int.floor`、`Int.ceil`。
[取整函数](../lean/examples/shifted_rounding_function/)把它们用于 `have fn`、嵌套调用、
带参数的 `thm` 和 `by thm`；三个例子的生成文件均已通过 Lean 检查。

[整数商和余数](../lean/examples/signed_integer_division/)支持负被除数及非零负模数，
`quot` 的除数则保留 `N+` 条件。[商余分解](../lean/examples/quotient_remainder_decomposition/)
对任意 `a Z, d N+` 证明 `a = d * quot(a, d) + a % d` 及余数上下界。
[商余函数](../lean/examples/integer_division_functions/)展示函数展开、参数等式替换和定理复用。
`have d N+` 及函数参数产生的正、非负、非零事实保留原 FactId，后续构造可以直接引用。

[最大公约数和最小公倍数](../lean/examples/gcd_lcm_values/)支持有符号整数计算。
`gcd(a, b)` 保留“至少一个非零”的条件，结果属于 `N+`；`lcm(a, b)` 属于 `N`，
允许 `lcm(0, 0) = 0`。[恒等式](../lean/examples/gcd_lcm_identities/)覆盖交换律、
绝对值关系和乘积关系；[欧几里得步骤](../lean/examples/gcd_euclidean_step/)覆盖
`gcd(a, b) = gcd(b, a % b)`。[函数示例](../lean/examples/gcd_lcm_functions/)还包含
带条件的 `have fn`、`thm`、`by thm` 和参数等式替换。四组生成文件均已通过 Lean 检查。
已有 gcd 对象作为模数时，非零条件从它的 WD 取得，不再另行证明。

[阶乘](../lean/examples/factorial_values/)保留参数属于 `N` 的证据，结果属于 `N+`，
通过已证明的接口对应到 `Nat.factorial`。[递推关系](../lean/examples/factorial_identities/)
和[单调性](../lean/examples/factorial_order/)均已接入；严格单调性保留较小参数属于
`N+` 的条件，因为 `0! = 1!`。[排列计数函数](../lean/examples/factorial_function/)
展示它在 `have fn` 中的定义与调用。

虚数单位写作 `i`，在既有数字包装中使用 `Complex.I`。
[具体复数计算](../lean/examples/imaginary_unit_values/)复核 result 中记录的实部和虚部；
[任意复数参数的多项式恒等式](../lean/examples/complex_polynomial_identity/)使用对应的
固定归一化过程。[旋转函数](../lean/examples/complex_rotation/)定义 `rotate(z) = i * z`，
再用命名定理和多步等式证明两次调用得到 `-z`。这些例子的生成文件均已通过 Lean。

[正负与非零数域](../lean/examples/signed_numeric_values/)补齐了 `Q+`、`Q-`、
`Z-`、`R-`、`Q*`、`Z*`、`R*`、`C*`。[对象声明](../lean/examples/signed_numeric_declarations/)
和[任意参数](../lean/examples/signed_numeric_domains/)产生的符号、非零事实沿用原 FactId，
后续除法 WD 可以直接引用。[带前提的成员断言](../lean/examples/refined_numeric_membership/)
消费原 result 中的基础数域与条件证明；[函数](../lean/examples/signed_numeric_functions/)
保留这些定义域和值域。[集合包含语句](../lean/examples/signed_numeric_subsets/)也已接入。
这些集合由现有 `SetSemantics` 的分离操作构造，没有增加模型字段或公理。

[正实数、非零有理数的乘除](../lean/examples/refined_products/)保留原操作数的成员证明和 WD。
[倒数函数](../lean/examples/nonzero_rational_reciprocal/)、
[正数缩放函数](../lean/examples/positive_scaling_functions/)和
[倒数乘积定理](../lean/examples/nonzero_rational_product_theorem/)把这些值域用于嵌套调用、
`thm` 和 `by thm`。[数值非成员关系](../lean/examples/numeric_nonmembership/)包括
`not 1 / 3 $in Z`、`not i $in R`；
[有限集合非成员关系](../lean/examples/finite_nonmembership/)包括 `not 4 $in {1, 2, 3}`，
以及由一个对象属于某集合、另一个不属于该集合推出两者不等。六组生成文件均已通过 Lean。

`have fn … by exist!` 现在可以从“每个合法输入都有唯一输出”的证明构造函数。
编译器消费原 result 中的全称证明、函数集合 WD 和成员／性质／唯一性三个存储结果，
后续调用引用原 FactId。例子包括[恒等函数](../lean/examples/selected_identity_function/)、
[带非零条件的倒数](../lean/examples/selected_reciprocal_function/)、
[两参数加法及计算](../lean/examples/selected_sum_function/)，以及
[任意集合上的恒等函数](../lean/examples/selected_set_identity_function/)。
四组源码和生成文件均通过实际 Lean 检查，生成文件约 13–28 KB。
目前支持顶层声明、一个输出变量和既有函数接口所支持的定义域；任意集合例子不要求集合非空。

`by contra` 已接入 `forall` 和 `not forall` 目标，包括
[带非零前提的倒数](../lean/examples/contradiction_with_reciprocal_guard/)；
[定理中的 `not forall` 前提](../lean/examples/negated_universal_premise/)也可以通过
`obtain` 取出反例。编译器沿用原 result 的参数、前提、WD 和 FactId，局部假设不会泄漏到外面。
四个新例子均通过实际 Lean 检查，生成文件约 2.4–8 KB。这批例子用原子事实结束反证。

`by contra` 也已接入 `exist!` 目标，包括
[两个实数坐标](../lean/examples/unique_pair_by_contradiction/)、
[带非零条件的倒数](../lean/examples/unique_guarded_value_by_contradiction/)、
[可调用的定理](../lean/examples/unique_copy_by_contradiction/)、
[任意集合对象](../lean/examples/unique_set_copy_by_contradiction/)和
[第二个变量依赖第一个变量的集合](../lean/examples/unique_dependent_pair_by_contradiction/)。
编译器消费原来的“另有一个不同候选”的全称假设，唯一性仍按对象表示的值比较。
六组生成文件均通过实际 Lean 检查。

`impossible` 也可以用整个量词命题结束反证：
[`forall`](../lean/examples/universal_contradiction_closing/)、
[带非零条件的 `forall`](../lean/examples/guarded_universal_contradiction_closing/)、
[`not forall`](../lean/examples/counterexample_contradiction_closing/)、
[`exist!`](../lean/examples/unique_contradiction_closing/)和
[两个变量的唯一存在](../lean/examples/unique_pair_contradiction_closing/)。
编译器先消费正反两条原始验证结果，再组合出矛盾。
[命名反例定理](../lean/examples/named_counterexample/)还展示了保存 `not forall`、
调用定理、用 `obtain` 取出反例的完整过程。

局部全称假设在 Lean 内部量化 `M.Value`，每次引用时转换输入对象的表示；
原对象和成员／前提的 FactId 保持不变。
[同一假设先用于数字、再用于一般对象](../lean/examples/counterexample_after_universal_use/)
已有实际检查，避免了局部假设被第一次使用固定到某个 Lean 类型层级的问题。
本批七组新例子和九组相关旧例子均通过严格 Litex、相同输出再生成和 Lean 4.31.0 检查；
43 个导出定理只使用标准公理。新增文件约 4–24 KB，没有修改 Runtime、result 类型或 `Litex.lean`。

`have fn … by cases` 已接入顶层分段函数声明和调用：
[绝对值](../lean/examples/piecewise_absolute_value/)、
[零点补定义的倒数](../lean/examples/piecewise_total_reciprocal/)、
[两个数取较大值](../lean/examples/piecewise_larger_value/)和
[带非零定义域的倒数绝对值](../lean/examples/piecewise_inverse_magnitude/)均通过实际 Lean 检查。
声明消费原 result 中的覆盖、互斥和返回值 WD 证明；调用保留选中分支的条件证明，
引用原 FactId 对应的分支等式。四份生成文件约 14–35 KB。
本批检查了一个／两个实数输入、两个分支和非零条件；倒数例子还包含任意非零输入的全称等式。
`Litex.lean` 用已有函数语义证明分段函数的构造和调用性质，没有增加语义公理。

函数性质也已接入：`$injective(A, B, f)`、`$surjective(A, B, f)`、
`$bijective(A, B, f)` 可以消费原来的定义证明，并按原 FactId 发布、引用推导事实。
可以看[恒等函数的双射证明](../lean/examples/identity_bijection/)、
[从单射和满射前提出发的推理](../lean/examples/mapping_property_inference/)、
[平移函数的双射证明](../lean/examples/shift_bijection/)，以及
[任意集合上双射的唯一原像](../lean/examples/bijective_unique_preimages/)。
唯一原像规则消费 result 中已有的双射引用和目标成员证明，支持等式的两个方向。
`Litex.lean` 在已有函数语义上定义这些性质并证明转换定理，没有增加模型字段或公理。
四份生成文件约 13–27 KB，均通过 Lean 4.31.0；28 个导出定理通过公理审计。
本批检查的是精确的一元函数签名；通过集合相等或有限前缀转换的 WD 路线，留待后续接入。

函数值域和取原像语句也已接入：

```litex
have fn shift(x R) R = x + 1
shift(2) $in fn_range(shift)
have by fn_preimage: a from shift(2) $in fn_range(shift)
a $in R
shift(a) = shift(2)
```

对应例子有[平移函数](../lean/examples/shift_range_preimage/)、
[倒数函数与非零原像](../lean/examples/reciprocal_range_preimage/)、
[双参数函数](../lean/examples/sum_range_preimage/)，以及
[任意集合上的值域成员](../lean/examples/function_range_members/)。
倒数例子还包含定理内部的局部取原像。四组均通过严格 Litex、相同输出再生成和
Lean 4.31.0 检查，生成文件约 9–55 KB。

`fn_range(f)` 的语义只由函数的图决定，提供 WD 的函数签名不会改变这个集合。
`Litex.lean` 从已有的分离和函数图性质证明值域、成员及原像定理，没有增加公理。
原 result 现在保留已经选中的函数签名、对应 FactId 和实际原像参数；编译器按这些
引用及返回的成员、条件、等式生成证明。取原像的存在性证明只生成一次，后续引用它；
原像处的函数调用用声明返回的成员和条件构造。Runtime 存储、证明搜索和源码 AST 没有改变。

[匿名函数调用的值域成员规则](../lean/examples/anonymous_function_ranges/)也已接入，
包括带非零条件的双参数除法。编译器消费原来的函数相等证据和调用 WD；匿名函数
只改绑定参数名时，先核对 alpha 等价，再生成对应的 Lean 自反证明。

原像还可以保留[正实数成员事实](../lean/examples/positive_range_preimage/)，
支持[两个正数坐标](../lean/examples/positive_pair_preimage/)，以及
[正数域与两个额外条件](../lean/examples/guarded_positive_preimage/)；最后一个例子
也在命名定理内部取原像。编译器按签名中的顺序拆出正性和显式条件，恢复每个 `R+`
成员事实，然后按原 FactId 发布条件。这四组补充例子均通过严格 Litex、相同输出
再生成和 Lean 4.31.0，生成文件约 15–95 KB，没有修改 Core 语义或 result 生产过程。

依赖型输入域和其他完整定义域证据分支仍待接入。固定数域上的嵌套匿名函数
现在可以捕获外层参数，见[定义后立即调用内层函数](../lean/examples/nested_function_application/)。

`sketch:` 会检查块内全部语句，然后丢弃这个局部作用域。编译器把原来的子结果放进
私有 Lean 证明块，保留外部引用和原 WD 编号，块内事实不会成为块外的源码事实。
可看[局部计算](../lean/examples/local_arithmetic_sketch/)、
[嵌套块](../lean/examples/nested_arithmetic_sketch/)、
[定理参数和引用](../lean/examples/sketch_in_named_theorem/)、
[tuple 坐标](../lean/examples/local_tuple_sketch/)和
[有限集成员](../lean/examples/local_finite_set_sketch/)；五组都已通过 Lean 检查。
块内语句仍遵守原有支持边界，例如局部 `have fn` 声明尚未接入。

整数区间现在也能用 `expand:` 展开：

```litex
claim:
    ? forall x range(1, 3):
        x = 1 or x = 2
    expand: x $in range(1, 3)
```

编译器读取原来的成员证明、完整枚举值和存储的析取事实，按原 FactId 输出。
`range(a, b)` 不含右端点，`closed_range(a, b)` 包含右端点；构造时保留整数端点
的 WD 和成员证据，推导出的整数性、上下界等事实也沿用原编号。
可看[源码与生成 Lean](../lean/examples/expand_half_open_integer_range/)，以及
[展开后分情况证明平方上界](../lean/examples/integer_range_square_bound/)的例子。
这批七组例子均通过 Lean 4.31.0，覆盖负数、单点区间和算式端点。展开要求端点能
精确算成整数、枚举长度为 1–1,024；区间构造和边界推理也支持任意整数端点。

`by for` 和 `by enumerate finite_set` 也支持在整数区间上逐项证明：

```litex
by for:
    ? forall n range(0, 4):
        n * n <= 9
    n * n <= 9
```

每个取值都使用 result 中原来的绑定、条件和证明步骤，编译器检查完整性与顺序，
最后引用已经生成的结论。可看[四个平方值](../lean/examples/integer_range_square_values/)、
[带非零条件的除法](../lean/examples/guarded_integer_range_division/)，以及
[命名定理中的循环证明](../lean/examples/named_integer_range_enumeration/)。
负数、空区间、单点区间和算式端点均有例子。也支持多个参数的组合：

```litex
by for:
    ? forall x range(0, 3), y range(0, 2):
        x * x + y * y <= 5
    x * x + y * y <= 5
```

可看[矩形范围内的平方和](../lean/examples/integer_rectangle_square_bound/)、
[两个非零条件](../lean/examples/nonzero_integer_pair_division/)和
[三个参数混用列表与区间](../lean/examples/finite_triple_product/)。同组参数可以共用一个域。
组合按源码顺序排列，最后一个参数变化最快；编译器检查全部赋值，总数上限为 1,024。
任一域为空时直接关闭证明。依赖前面参数的枚举域仍未接入。

不等式还覆盖四种加法规则：加上非负项保留下界，加上非正项保留上界，加数左右互换也支持。
可看[加法下界](../lean/examples/weak_additive_lower_bounds/)和
[加法上界](../lean/examples/weak_additive_upper_bounds/)。放宽数值界限时，编译器引用原来的
FactId，检查整数端点及严格性，再使用传递性。例如 `x < 4` 或 `x <= 4` 都可以推出
`x < 6`；可看[数值下界](../lean/examples/weaken_numeric_lower_bounds/)和
[数值上界](../lean/examples/weaken_numeric_upper_bounds/)。这些规则也能用于
[枚举中的和式上界](../lean/examples/integer_rectangle_sum_bound/)及
[命名定理](../lean/examples/named_integer_rectangle_sum/)。

两条不等式也能相加：由 `a <= b` 和 `c <= d` 得到 `a + c <= b + d`，
其中任一条换成严格不等式，就得到严格的和式上界。弱不等式还支持加数交叉配对。
可看[两项求和](../lean/examples/componentwise_sum_bounds/)、
[严格与非严格界混合](../lean/examples/mixed_strict_sum_bounds/)和
[分两步合并三项并调用定理](../lean/examples/three_term_sum_bound/)。
编译器保留 result 中的两条原始证据、配对位置和严格性。

减法支持由 `a <= b` 得到 `a-c <= b-c`，以及 `c-b <= c-a`，也支持严格不等式。
可看[共同减数](../lean/examples/subtract_shared_value/)和
[共同被减数](../lean/examples/subtract_from_shared_value/)。
[差为实数的例子](../lean/examples/real_difference_domains/)中，共同项声明属于 `C`，
比较使用两个差属于 `R` 的事实，保留共同项原来的表示。
[严格传递性](../lean/examples/strict_order_chains/)引用两条原有界限；
[三步差值估计](../lean/examples/ordered_difference_bound/)把减法、传递性和定理调用组合起来。

二元交集 `intersect(A, B)` 支持构造、成员引入、两侧成员推论和包含关系。
可看[成员事实](../lean/examples/intersection_membership/)、
[包含关系](../lean/examples/intersection_subset_bounds/)、
[命名交集](../lean/examples/named_intersection/)及
[嵌套交集与定理调用](../lean/examples/intersection_reassociation/)。
Lean 表示复用已有的有界集合构造；推出的两条成员事实保留原来的 FactId。

集合等式还支持交集、并集的交换律、结合律、幂等律和空集规则，
以及[交集对并集的分配律](../lean/examples/intersection_distributes_over_union/)、
[根据包含前提化简交集](../lean/examples/intersection_from_subset/)。
可看[交集等式](../lean/examples/set_intersection_identities/)、
[并集等式](../lean/examples/set_union_identities/)和
[等式反写](../lean/examples/set_identity_symmetry/)。
每个选中的 builtin 对应一个已证明的 Lean 定理；有条件的化简引用原来的包含关系证明。

差集 `set_minus(A, B)` 支持[成员及其推论](../lean/examples/set_difference_membership/)、
[排除与包含关系](../lean/examples/set_difference_exclusion/)、
[空集化简和德摩根律](../lean/examples/set_difference_identities/)。
这些规则可以用于[嵌套差集的命名定理](../lean/examples/set_difference_theorem/)
和[返回集合的函数](../lean/examples/set_difference_function/)。
[并集对交集的分配律](../lean/examples/union_distributes_over_intersection/)也支持因子换序和等式反写。

[连续作差](../lean/examples/consecutive_set_difference/)可以合并为排除一个并集。
包含关系支持[差集和幂集的单调性](../lean/examples/set_containment_monotonicity/)、
[并集的上界](../lean/examples/union_containment_bounds/)、
[嵌套集合运算及包含关系传递](../lean/examples/nested_set_containment/)。
[不属于集合的事实](../lean/examples/set_operator_nonmembership/)也可以沿交集、并集传递。
这些步骤组合成了[并集作差的包含定理](../lean/examples/union_difference_bound/)
和[交并集排除定理](../lean/examples/outside_union_intersection/)，两个例子都包含后续定理调用。

集合对象 `preimage(f, y)` 和 `preimage_set(f, Y)` 也已接入：分别表示输出等于
`y`、输出属于 `Y` 的合法输入，保留原来的输入集合及非零等条件。成员事实可以推出
这些条件和输出事实，后续语句引用原 FactId；也支持原像集包含于输入集合。
双参数输入使用原来的笛卡尔积元组表示。可看[倒数函数的原像集](../lean/examples/guarded_reciprocal_preimages/)、
[双参数商函数](../lean/examples/binary_quotient_preimages/)、
[抽象函数](../lean/examples/abstract_function_preimages/)及
[正实数定义域](../lean/examples/positive_domain_preimages/)。四组源码、实际生成文件均通过
严格 Litex、相同输出再生成和 Lean 4.31.0 检查，生成文件为 18–81 KB。
Core 从已有的分离和函数图性质证明所需定理；本批没有修改 Runtime、AST 或 result 生产过程。

函数对象 `compose(f, g)` / `f ∘ g` 也已接入。它保留 `g` 的完整定义域，
构造时证明每个合法输入的 `g` 值都满足 `f` 的输入条件。编译器支持构造、函数集合
成员事实、调用、输出成员事实，以及 result 记录的复合展开步骤。可看
[差的平方](../lean/examples/squared_gap_composition/)、
[平移后平方](../lean/examples/shifted_square_composition/)、
[两次倒数](../lean/examples/double_reciprocal_composition/)、
[任意实函数](../lean/examples/abstract_function_composition/)和
[正实数输入域](../lean/examples/positive_domain_composition/)。五组源码与生成文件均通过
严格 Litex 和 Lean 4.31.0 检查。[函数图等式](../lean/examples/composition_graph_laws/)
还覆盖结合律、左右单位律、复合等于展开函数，以及复合值域包含于外层函数值域。
展开函数可以具有更宽的已验证返回集合。[非零定义域的单位律](../lean/examples/guarded_composition_identities/)
保留完整定义域条件，[抽象结合律](../lean/examples/abstract_composition_associativity/)接受任意实函数参数。
这三组也通过了实际 Lean 检查。定义域匹配还支持 result 记录的双向包含证明：
编译器核对参数、成员条件和前提，引用原 FactId，再用集合外延性得到定义域相等。
右单位律和 `by fn_extension` 共用这一过程；后者的定义域事实保留在原局部作用域中。
可看[正数上的平移](../lean/examples/equal_positive_shifts/)和
[重排定义域条件](../lean/examples/reordered_function_domains/)。
`by fn_extension` 还支持两个参数和 `R+` 输入，见
[双参数求和](../lean/examples/equal_binary_sums/)和
[带非零条件的商](../lean/examples/equal_guarded_quotients/)。
超过两个参数、依赖前面参数的输入集合，以及其他尚未接入的完整定义域证据仍会拒绝。
复合函数构造对输入打包表示切换的限制仍然保留。

`release thm fn_set_member(...)` 和选取结论的 `by thm fn_set_member(...)`
也会先编译定义域双向包含，再编译原有的返回值证明。例子包括
[重排条件](../lean/examples/reordered_function_membership/)、
[`R+` 与显式正数条件](../lean/examples/positive_function_membership/)、
[任意函数参数](../lean/examples/abstract_function_membership_domains/)和
[复合函数](../lean/examples/composed_quotient_membership/)。
这里保留函数的完整定义域；要限制到较小定义域，仍须构造相应的限制函数。


函数参数还可以返回另一个函数，调用时逐层保留参数和定义域证明：

```litex
forall provider fn(t R: t != 0) fn(x, y R: y != 0) R:
    provider(2)(3, 4) $in R
```

[连续调用](../lean/examples/returned_function_values/)包含两层和三层调用；
返回的函数还可以[取值域](../lean/examples/returned_function_ranges/)、
[取原像](../lean/examples/returned_function_preimages/)，以及通过
[命名定理把实数返回值看作复数返回值](../lean/examples/returned_function_membership/)。
这四组均通过严格 Litex 和 Lean 4.31.0 检查。编译器直接读取 `ApplicationReturn`
里的签名引用、参数 WD、条件证明及局部 WD ID，再调用已有的 Lean 语义定理。
目前返回签名是固定的；依赖返回类型，以及多层调用后再恢复完整定义域的路线还没接入。

`have fn` 还可以构造返回的函数，或者接收并返回一个函数参数：

```litex
have fn selected_shift(t R) fn(x R) R = fn(x R) R {x + 1}
have fn keep_function(f fn(x R) R) fn(y R) R = f
forall f fn(x R) R:
    keep_function(f) = f
```

[返回平移函数的例子](../lean/examples/selected_shift_function/)还给结果起别名、记录函数签名，
并证明 `chosen_shift(2) = 3`；[函数上的恒等算子](../lean/examples/function_identity_operator/)
验证了函数参数和函数返回值。[匿名函数的成员证明](../lean/examples/literal_function_signatures/)
支持参数改名，同时保留输入集合、返回集合及一／两个参数的非零条件。
这三组均通过严格 Litex 和 Lean 4.31.0 检查，复用已有语义和原始 WD 证据。
返回的数值函数还可以捕获外层参数：

```litex
have fn shifted_by(t R) fn(x R) R = fn(x R) R {x + t}
forall t R:
    shifted_by(t) = fn(x R) R {x + t}
    shifted_by(t)(2) = 2 + t
```

[平移函数](../lean/examples/captured_shift_functions/)还包含正实数成员事实；
[除法函数](../lean/examples/captured_division_functions/)分别检查外层和内层的非零条件；
[双参数函数](../lean/examples/captured_binary_functions/)检查两个输入与捕获值一起参与计算。
加上[内层函数立即调用](../lean/examples/nested_function_application/)，四组均通过严格 Litex
和 Lean 4.31.0。编译器保留原始 WD 和参数 ID，按结果重放替换及后续调用，
没有修改 Runtime 或增加语义公理。依赖参数的输入／返回集合仍待接入。

**Litex 已经在一个明确的数学子集上打通了从源码证明、编译生成 Lean 到 Lean 复核的流程：
标准数域上的初等代数与不等式，配上基础集合、带定义域的函数和可复用定理。**
这些能力可以组合使用，处理带任意参数、前提和中间步骤的证明；已有案例还通过手写
Adapter 导出普通 Lean／Mathlib 定理。

| 数学层面 | 当前覆盖的主要内容 | 对应示例 |
| --- | --- | --- |
| 数 | ℕ、ℤ、ℚ、ℝ、ℂ，以及正数、负数、非零子集；15 种源码数域都有表示，参数保留原来的宿主表示。 | [数域包含链](../lean/examples/numeric_hierarchy/)、[正负与非零参数](../lean/examples/signed_numeric_domains/)、[集合包含语句](../lean/examples/signed_numeric_subsets/) |
| 运算与关系 | 精确分数与有限小数、四则、多项式与有理式恒等式、消去律；部分固定整数幂和实数不等式规则。 | [精确分数与小数](../lean/examples/exact_fractions_and_decimals/)、[平方差](../lean/examples/real_difference_of_squares/)、[消去律](../lean/examples/multiplicative_cancellation/)、[平方非负](../lean/examples/real_squares_nonnegative/) |
| 集合 | 任意集合参数、空集、有限枚举、有界集合构造，以及成员、子集和相关推理。 | [任意集合](../lean/examples/arbitrary_set_laws/)、[有限集合](../lean/examples/finite_natural_set/)、[闭单位区间](../lean/examples/closed_unit_interval/) |
| 函数 | 一个或两个数值参数的公式函数，显式定义域条件、求值与组合；已有互逆和单射的完整案例。 | [带条件的双参数函数](../lean/examples/two_argument_shifted_quotient/)、[函数组合](../lean/examples/composed_real_formula/)、[有理函数的互逆与单射](../lean/examples/rational_inverse_maps/) |
| 结构 | 顶层集合／非空集合／对象参数、独立字段，原子／扁平合取／链式定义条件，元组成员关系、量化与声明对象、给定值的别名、显式展开、直接字段访问与数值字段运算；支持任意集合及嵌套元组实例。 | [通用坐标对](../lean/examples/parameterized_pairs/)、[指定第一坐标](../lean/examples/designated_coordinate_pairs/)、[正坐标点](../lean/examples/positive_point_conditions/)、[带非零条件的比值](../lean/examples/positive_ratio_conditions/) |
| 定义与证明 | 具体谓词、顶层抽象谓词、全称与条件命题、等式链、部分合取、命名定理及调用、局部对象、`let`、`claim` 和 `sketch`。 | [抽象性质](../lean/examples/abstract_property_transport/)、[谓词与等式替换](../lean/examples/concrete_predicate_equality_transport/)、[定理返回与调用](../lean/examples/named_compound_theorem_returns/)、[局部对象](../lean/examples/local_witness_additive_identity/)、[claim 与正数值域](../lean/examples/newton_positive_update/) |

这里的覆盖指已实现并检查过的构造和证明路线，并不意味着该领域内任意 Litex 证明都能编译。
绝对值、符号自然幂和部分析取也已有受限规则的编译及局部 Lean 检查；递归 Newton
估计的生成 Lean 证明已通过检查，原生全指标接口仍未完成，状态见 [Newton 示例说明](examples/litex_to_lean/newton_residual/README.md#recursive-residual-bound)。

可以先读[加零的完整编译与 Adapter 示例](examples/litex_to_lean/add_zero/README.md)，
再看[有理函数互逆的完整流程](#两个有理函数从定义到原生等价)。
上表每个示例目录都把 `.lit` 源码和实际生成的 `.lean` 放在一起；继续浏览
[全部源码／生成文件对](../lean/examples/)，就能看到这些数学能力如何组合成可供 Lean 使用的证明。
