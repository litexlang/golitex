# PostProcess 功能索引

本文档列出了所有在 `environment` 包中的 postprocess 功能，用于在添加新事实后自动推导出相关事实。

## 文件结构

### 1. `env_new_fact.go`
主入口文件，包含：
- `NewFact()` - 事实添加的入口函数
- `newSpecFact()` - SpecFact 的处理入口，会调用相应的 postprocess
- `isTrueEqualFact_StoreIt()` - 等号事实的存储和处理，会调用 equal fact postprocess

### 2. `env_new_fact_post_process.go`
Pure Fact 和 Exist_St Fact 的 postprocess：
- `newPureFactPostProcess()` - Pure Fact 的 postprocess 分发器
- `newExist_St_FactPostProcess()` - Exist_St Fact 的 postprocess 分发器
- `newTrueExist_St_FactPostProcess()` - TrueExist_St Fact 的处理
- `newFalseExist_St_FactPostProcess()` - FalseExist_St Fact 的处理
- `newFalseExistFact_EmitEquivalentUniFact()` - FalseExist 转换为 UniFact
- `equalSetFactPostProcess()` - equal_set 事实的处理
- `equalTupleFactPostProcess()` - equal_tuple 事实的处理

### 3. `env_equal_fact_post_process.go`
等号事实的 postprocess：
- `equalFactPostProcess_cart()` - 处理 `x = cart(x1, x2, ..., xn)`
- `equalFactPostProcess_tuple()` - 处理 `obj = tuple`
- `equalFactPostProcess_tupleTuple()` - 处理 `tuple = tuple`
- `equalFactPostProcess_tupleEquality()` - tuple 相等性的统一处理入口
- `equalFactPostProcess_listSetEquality()` - 处理 `x = {1, 2, 3}`

### 4. `env_builtin_prop_post_process.go`
内置属性的 postprocess：
- `BuiltinPropExceptEqualPostProcess()` - 内置属性（除等号外）的 postprocess 分发器
- `inFactPostProcess()` - `$in` 事实的处理（调用 `env_new_in_fact_post_process.go` 中的函数）
- 比较操作的 postprocess：
  - `builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero()`
  - `builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsNotZero()`
  - `builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsZero()`
  - `builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsNotZero()`
  - `builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero()`
  - `builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsNotZero()`
  - `builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsZero()`
  - `builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero()`
- `subsetOfFactPostProcess()` - `subset_of` 事实的处理

### 5. `env_new_in_fact_post_process.go`
`$in` 事实的 postprocess：
- `inFactPostProcess()` - `$in` 事实的处理入口
- `inFactPostProcess_TryFnTemplate()` - 处理 `$in fnTemplate(...)`
- `inFactPostProcess_TryFnTemplateFnObj()` - 处理 `$in fnTemplateFnObj`
- `inFactPostProcess_TryCart()` - 处理 `$in cart(...)`
- `inFactPostProcess_InCart()` - cart 集合的 `$in` 处理
- `inFactPostProcess_InFnTemplate()` - fnTemplate 的 `$in` 处理
- `inFactPostProcess_TryListSet()` - 处理 `$in listSet(...)`
- `inFactPostProcess_InListSet()` - listSet 的 `$in` 处理
- `inFactPostProcess_TrySetBuilder()` - 处理 `$in setBuilder(...)`
- `inFactPostProcess_InSetBuilder()` - setBuilder 的 `$in` 处理
- `inFactPostProcess_TryRangeOrClosedRange()` - 处理 `$in range(...)` 或 `$in closed_range(...)`
- `inFactPostProcess_TryNPos()` - 处理 `$in NPos`

## PostProcess 调用流程

```
NewFact()
  └─> newSpecFact()
      ├─> isTrueEqualFact_StoreIt() (如果是等号事实)
      │   ├─> equalFactPostProcess_cart()
      │   ├─> equalFactPostProcess_tupleEquality()
      │   └─> equalFactPostProcess_listSetEquality()
      │
      └─> postprocess (如果不是等号事实)
          ├─> newExist_St_FactPostProcess() (如果是 Exist_St Fact)
          │   ├─> newTrueExist_St_FactPostProcess()
          │   └─> newFalseExist_St_FactPostProcess()
          │
          └─> newPureFactPostProcess() (如果是 Pure Fact)
              ├─> BuiltinPropExceptEqualPostProcess() (如果是内置属性)
              │   ├─> inFactPostProcess() (如果是 $in)
              │   │   └─> 各种 inFactPostProcess_Try* 函数
              │   ├─> 各种比较操作的 postprocess
              │   ├─> equalSetFactPostProcess()
              │   ├─> equalTupleFactPostProcess()
              │   └─> subsetOfFactPostProcess()
              │
              ├─> newTruePureFact_EmitFactsKnownByDef() (如果是用户定义的 prop)
              └─> newFalseExistFact_EmitEquivalentUniFact() (如果是 FalseExist)
```

## 主要 PostProcess 功能说明

### Equal Fact PostProcess
当添加等号事实时，会自动处理：
1. **Cart 相等**: `x = cart(x1, x2, ..., xn)` → 生成 `is_cart(x)`, `dim(x) = n`, `proj(x, i) = xi`
2. **Tuple 相等**: `obj = tuple` 或 `tuple = tuple` → 生成逐元素相等事实
3. **List Set 相等**: `x = {1, 2, 3}` → 生成 OR 事实和 `count(x) = len`, `is_finite_set(x)`

### In Fact PostProcess
当添加 `$in` 事实时，会根据右侧类型自动处理：
1. **FnTemplate**: 推导出模板相关的 uni fact
2. **Cart**: 生成 `a[i] $in cartSet.Params[i]` 和 `dim(a) = len`
3. **ListSet**: 生成 OR 事实表示等于其中一个元素
4. **SetBuilder**: 实例化集合构造器中的事实
5. **Range/ClosedRange**: 生成数值范围相关的事实
6. **NPos**: 生成 `$in N`, `$in Q`, `$in R`, `> 0`, `>= 1` 等事实

### Builtin Prop PostProcess
内置属性的特殊处理：
1. **比较操作**: 当右侧为 0 时，自动生成 `!= 0` 等事实
2. **equal_set**: 生成 `a = b` 事实
3. **equal_tuple**: 生成逐元素相等事实
4. **subset_of**: 生成子集相关的事实

### Pure Fact PostProcess
Pure Fact 的处理：
1. **Transitive Prop**: 更新传递性属性的内存
2. **用户定义的 Prop**: 根据定义中的 iff 和 implication 规则推导事实
3. **Exist Prop**: FalseExist 转换为 UniFact

### Exist_St Fact PostProcess
Exist_St Fact 的处理：
1. **TrueExist_St**: `have(exist ... st ...)` → `exist` 和相关 iff/then 事实
2. **FalseExist_St**: 目前为空实现

