<a id="litex-to-lean-compiler-guide"></a>

# Litex 到 Lean 编译器指南

本指南通过具体的源码与生成结果示例，解释 Litex 到 Lean 编译的设计原则。它是持续维护的阅读入口，说明编译器为什么这样工作，以及输出意味着什么。

[编译器 README](../src/compile_to_lean/README.md)描述实现细节、内部设计理由、结果类型和扩展点。面向读者的解释和示例讲解放在这里；Rust 控制流与重放记录放在那里。[CLI 文档](Litex命令行参考.md#lean-compiler-boundary)负责命令行契约。

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
一般析取筛选、nonempty/finite 参数种类、无界理解、幂集／像与存在式集合选择
仍在编译边界外，不会被变成公理。

## 公式函数与具体谓词

[带保护条件的倒数](../lean/examples/guarded_real_reciprocal/statement.lit)用普通非零要求定义公式：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

生成的对象使用 `Litex.formulaFn`，求值使用 `Litex.call`。调用的 WD 包含记录的函数空间成员关系、参数成员关系及保护条件证明。对存储的源码证明的引用使用原始 `h_<FactId>` 名称。新检查的数值要求也可直接包含选定的证明表达式。`hf` 等库参数名不会重命名源码引用。

`FunctionSemantics M` 为数值接口增加图构造与求值。具体实例用 Mathlib 的 ZF 集合证明这些规律；源码函数仍是拥有自身身份的图对象。内部值函数体回调不会把源码对象替换为原生实数函数箭头。

当前切片支持一个或两个 N/Z/Q/R/C 输入及输出、数值域／值域别名、先前函数的公式复合，以及直接或具体谓词保护条件。顶层具体谓词可以使用已支持的平坦原子、And 和数值链条款。[非负性](../lean/examples/nonnegative_real_property/statement.lit)展示谓词定义与展开；[商的分配](../lean/examples/real_quotient_distributes/statement.lit)展示两个参数；[带保护条件的复合商](../lean/examples/two_argument_shifted_quotient/statement.lit)展示复合调用。编译消费每次调用实际捕获的 WD 和定义域证据。递归、归纳、高阶函数和量化谓词仍不在本期范围。

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

任意集合有一个明确的接口差异：`$is_set(A)` 在生成端有证明，原生端的
`A : ZFSet` 则通过类型表达集合身份，无需发明额外的原生 sethood 谓词。
整个集合的数值视图仍需 subset 证据。模块、一般存在式见证证明、无界理解、
存在式集合选择、递归／高阶函数体和局部 prop／fn／嵌套 thm，
以及未审查的推理／证书路线仍在编译边界外。
在结果中观察到未被消费的 inference 节点，不代表编译器已支持该推理。

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

这个例子也保留当前实现的实际成本：维护中的源码在最终单射证明里显式列出非零事实
并展开公式。更短的函数同余等式链可以通过 Litex 验证，却可能选中当前编译器尚未
支持的路线，因此源码验证成功还不够。
[直接 Mathlib 版本](examples/litex_to_lean/rational_inverse_maps/DirectLean.lean)
提供独立的作者写法对照。比较时应分别考察数学步骤、显式定义域证明和手写 Adapter
的工作量；生成证明的长度不能代表源码作者的工作量。这个例子展示连续、可复用的
编译成果，不据此宣称编写或运行速度更快。

## Newton 迭代：下一个完整实验

[Newton 残差实验](examples/litex_to_lean/newton_residual/Experiment.md)的目标是从
`x_0 = 1`、`x_(n+1) = (x_n + 2/x_n)/2`，证明所有自然数上的
`|x_n^2 - 2| <= 4*(1/4)^(2^n)`。证明串起除法合法性、残差恒等式、迭代下界、
二次收缩以及两个归纳。现有完整 Litex 源码通过当前严格验证，独立的手写 Lean
对照也通过检查；完整证明尚未接通编译器。

已接通的是其中的[单步恒等式源码](../lean/examples/newton_residual_identity/statement.lit)
和[实际生成的 Lean](../lean/examples/newton_residual_identity/statement.lean)。
[Adapter](examples/litex_to_lean/newton_residual/Adapter.lean) 消费生成证明，
[Final](examples/litex_to_lean/newton_residual/Final.lean) 提供已检查的普通 Lean 接口：

```lean
theorem newtonResidualIdentity (x : ℝ) (hx : x ≠ 0) :
    ((x + 2 / x) / 2)^2 - 2 = ((x - 2 / x) / 2)^2 := by
  exact Adapter.newtonResidualIdentity x hx
```

这部分通过 pinned Lake 检查，证明依赖确实经过 Adapter 到达生成的定理，且只依赖
标准 Lean 公理。完整实验仍需接入正实数函数值域、证明块、绝对值、自然数符号幂、
递归定义和归纳；实验说明逐项记录了实际拒绝边界与验收顺序。这里的界是方程残差，
并非到 `sqrt(2)` 的距离，也不提前声称 Litex 比手写 Lean 更短。

## 维护本指南

新增设计说明应连接到 [lean/examples/](../lean/examples/)下真实的源码/生成文件对。每个讲解都应说明数学事实、选定的源码证明路线、生成证明保留什么，以及最近的不支持边界。明确标注拟议设计与未验证示例。

以上代码片段来自维护中的示例与语义接口，不是完整的能力清单。其所属产物改变时，应同步更新。实现映射保留在[编译器 README](../src/compile_to_lean/README.md)中；开发夹具、验收记录与构建工具保留在仅限本地的编译器工作区 `scripts/litex_to_lean/`。
