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

## 公式函数与具体谓词

[带保护条件的倒数](../lean/examples/guarded_real_reciprocal/statement.lit)用普通非零要求定义公式：

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

生成的对象使用 `Litex.formulaFn`，求值使用 `Litex.call`。调用的 WD 包含记录的函数空间成员关系、参数成员关系及保护条件证明。对存储的源码证明的引用使用原始 `h_<FactId>` 名称。新检查的数值要求也可直接包含选定的证明表达式。`hf` 等库参数名不会重命名源码引用。

`FunctionSemantics M` 为数值接口增加图构造与求值。具体实例用 Mathlib 的 ZF 集合证明这些规律；源码函数仍是拥有自身身份的图对象。内部值函数体回调不会把源码对象替换为原生实数函数箭头。

当前切片支持一个或两个固定 N/Z/Q/R/C 输入及输出、原子函数保护条件，以及定义体为平坦原子条款的顶层具体谓词。[非负性](../lean/examples/nonnegative_real_property/statement.lit)展示谓词定义与展开；[商的分配](../lean/examples/real_quotient_distributes/statement.lit)展示两个参数。递归或复合公式体，以及使用具体谓词的函数保护条件，仍是不支持的编译路线。

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

编译器检查记录的非空性证明，输出一般的已认证对象和属于 R 的假设。后续定理头部保留这些参数；它不会把对象定义为零。此阶段的任意 have 支持范围是顶层数值上下文；局部见证/证明声明还需要后续支持。

[实数平方](../lean/examples/real_squares_nonnegative/statement.lit)和[弱序传递性](../lean/examples/weak_order_transitivity/statement.lit)使用普通的 `Litex.Le`/`Litex.Lt` 事实；大于比较通过交换参数表达。其含义包含实数指称见证；任意复数对象上没有序。编译器先重放实际的 R 定义域条件，再应用选定的序定理，并保留源码前提、精确引用和偶指数限制。

<a id="membership-preserves-the-objects-representation"></a>

## 成员关系保留对象表示

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
(_h_param_i1 : Litex.In _value_i1 (Litex.C (M := M)))
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
Litex.div _value_i1 _value_i2 _h_param_i1 _h_param_i2 _h_dom_f1
```

三个证明参数分别认证两个操作数的定义域与分母非零。它们保留源码条件，而不是新增数学操作数。输出相等证明之前，编译必须建立或解析这份精确的构造证据。

<a id="citations-and-assumptions-retain-their-scopes"></a>

## 引用与假设保留各自作用域

在除法示例中，`b != 0` 属于全称定理的局部上下文。它不能成为无关的后续定理的前提。局部对象、缓存的 WD 证据和引用事实也受同样限制。

重放通过记录的 ID 识别引用，并检查其主体。缓存的构造必须解析到该对象已经重放的证据。如果 ID 缺失，或必需的推导事实没有受支持的产生者，编译会拒绝该路线。在实时环境中寻找另一条真事实，会掩盖缺失的源码依赖。

直接标量消去现在可以从已存储的 `a+k=b+k`、`a-k=b-k`、`k-a=k-b` 发布 `a=b`，也可以在有 `k!=0` 证书时从 `a*k=b*k` / `a/k=b/k` 发布该事实。`k/a=k/b` 还要求两个分母均非零。Litex 保留了其推导证据，但当前编译器尚不重放这些证据。引用该推导等式会在 `FactId/Producer` 处拒绝编译；绝不会把它输出为新假设。测试 `equality_cancellation_lean_citations_fail_closed_without_infer_replay` 检查了这个产生者/消费者边界。

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

<a id="maintaining-this-guide"></a>

## 维护本指南

新增设计说明应连接到 [lean/examples/](../lean/examples/)下真实的源码/生成文件对。每个讲解都应说明数学事实、选定的源码证明路线、生成证明保留什么，以及最近的不支持边界。明确标注拟议设计与未验证示例。

以上代码片段来自维护中的示例与语义接口，不是完整的能力清单。其所属产物改变时，应同步更新。实现映射保留在[编译器 README](../src/compile_to_lean/README.md)中；开发夹具、验收记录与构建工具保留在仅限本地的编译器工作区 `scripts/litex_to_lean/`。
