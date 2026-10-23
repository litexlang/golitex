# Litex / Lean 检查耗时对照

本目录把到目前为止做过的 Litex / Lean 计时实验集中到一处：每一条用例在两侧写同一个数学命题，分别测量各自的检查路径，并保留可复现的源码、原始样本和环境快照。

```text
cases/            本轮用例定义（JSON：Litex 源码、Lean 命题、每条 Lean 证明路线）
sources/          每例的 Litex 与 Lean 源码，按批次与领域分目录
harness/bench.py  重跑计时（validate / measure / all）
results/          原始样本、汇总、验证记录、环境快照
```

## 怎么读这些数字

- 单位毫秒，数值为暖样本中位数；**倍率 = Lean ÷ Litex**，大于 1 表示 Litex 更快。
- 两侧都**不含**进程启动和 `import Mathlib`。完整的命令行耗时另有一套数量级更大的数字，不在这里混算。
- Litex：release 构建，每个样本新建严格 `Runtime`；计时覆盖词法、解析、良定义性检查、验证、存储与证据构建。
- Lean：`#probe` 自定义命令用纳秒时钟包裹 `elabCommand`，`Elab.async=false` 让证明构造与内核检查同步；计时不含命令解析。
- 这些是两条**检查路径**的对照，不是语言或内核的总体排名，也不是作者完成数学任务所需时间的同比缩短。

## 总览

| 领域 | 例数 | 倍率范围（Lean ÷ Litex） |
| --- | ---: | ---: |
| 自然数算术与根式 | 2 | 14× – 37× |
| 有限求和 | 4 | 3.5× – 7.3× |
| 三角 | 3 | 10× – 19× |
| 初等计算：对数、根式、大数 | 5 | 7× – 217× |
| 数论：素性与最大公因数 | 2 | 2.2× – 147× |
| 量词、见证、唯一存在、存在消去 | 21 | 1.1× – 77× |
| 定义与证明命令（函数、谓词、结构、反证、分类、归纳） | 10 | 0.5× – 51× |
| 集合 | 3 | 4.7× – 98× |
| 函数（值域、复合） | 2 | 0.1× – 3.8× |
| 整数算术与整除 | 2 | 8.4× |
| 有限组合 | 2 | 6.2× – 61× |
| 微积分（连续、导数） | 2 | 35× – 58× |
| 经典大证明（√2 无理，两侧同步骤） | 1 | 29× |

函数复合（0.14×）与递归定义（0.48×）是 Litex 变慢的两个方向，原因见[下面](#litex-变慢的地方)。

---

## 一、已有的五批实验

这五批的原始样本保存在本仓库的本地批次记录里（五个 `2026-10-22-*` / `2026-10-23-*` 目录）。这里发布的是每例的源码与汇总数字；这些数字是读取当时的记录，没有重新测量，环境见 `results/`。

### 1. 基础算术与根式（2026-10-22）

| 数学语句 | Litex | Lean 最快 | 倍率 | Lean 路线 | 源码 |
| --- | ---: | ---: | ---: | --- | --- |
| `1 + 1 = 2`（Mathlib 已载入） | 0.037 | 1.361 | **36.66×** | `rfl` | [lit](sources/arithmetic/add.lit) · [lean](sources/arithmetic/mathlib_nat.lean) |
| `sqrt(1) = 1` | 0.039 | 0.555 | **14.28×** | `Real.sqrt_one` | [lit](sources/arithmetic/sqrt.lit) · [lean](sources/arithmetic/sqrt_exact.lean) |

### 2. 有限求和与三角（2026-10-22）

| 数学语句 | Litex | Lean 最快 | 倍率 | Lean 路线 | 源码 |
| --- | ---: | ---: | ---: | --- | --- |
| `sum(1,10,fn(k Z) Z {k}) = 55` | 1.623 | 5.622 | **3.46×** | `decide` | [lit](sources/sums/sum_id_10.lit) |
| `sum(1,10,fn(k Z) Z {k^2}) = 385` | 2.224 | 8.266 | **3.72×** | `decide` | [lit](sources/sums/sum_sq_10.lit) |
| `sum(1,10,fn(k Z) Q {1/3}) = 10/3` | 2.123 | 11.277 | **5.31×** | `sum_const` + `norm_num` | [lit](sources/sums/sum_rat_10.lit) |
| `finite_set_sum({1,3,5,7,9}, fn(k Z) Z {k}) = 25` | 1.108 | 8.051 | **7.26×** | `decide` | [lit](sources/sums/finite_set_5.lit) |
| `sin(0) = 0` | 0.041 | 0.757 | **18.43×** | `Real.sin_zero` | [lit](sources/sums/sin_zero.lit) · [lean](sources/sums/sin_zero__exact.lean) |
| `sin(pi) = 0` | 0.040 | 0.736 | **18.50×** | `Real.sin_pi` | [lit](sources/sums/sin_pi.lit) · [lean](sources/sums/sin_pi__exact.lean) |
| `forall x R: sin(x)^2 + cos(x)^2 = 1` | 0.446 | 4.636 | **10.40×** | `fun x => Real.sin_sq_add_cos_sq x` | [lit](sources/sums/sin_identity.lit) · [lean](sources/sums/sin_identity__exact.lean) |

有限求和是这批里倍率最低的一类：两边都在逐项求和，Litex 的优势来自没有证明项构造。

### 3. 初等计算、数论与大数（2026-10-22）

| 数学语句 | Litex | Lean 最快 | 倍率 | Lean 路线 | 源码 |
| --- | ---: | ---: | ---: | --- | --- |
| `log(2,8) = 3` | 0.064 | 13.992 | **217.01×** | 显式重写（`logb_pow` 等） | [lit](sources/elementary/log_2_8.lit) · [lean](sources/elementary/log_2_8_explicit.lean) |
| `sqrt(2)*sqrt(8) = 4` | 0.240 | 7.077 | **29.50×** | `sqrt_mul` + `norm_num` | [lit](sources/elementary/radical_product.lit) |
| `$prime(1000000007)` | 0.027 | 4.029 | **147.19×** | `native_decide` | [lit](sources/elementary/prime_1000000007.lit) · [lean](sources/elementary/prime_1000000007_native_decide.lean) |
| `factorial(50) = 30…000`（精确值） | 0.107 | 2.501 | **23.41×** | `norm_num` | [lit](sources/elementary/factorial_50.lit) · [lean](sources/elementary/factorial_50_norm_num.lean) |
| `95800^4+217519^4+414560^4 = 422481^4` | 0.264 | 11.098 | **42.03×** | `rfl` | [lit](sources/elementary/fourth_power_eq.lit) · [lean](sources/elementary/fourth_power_eq_rfl.lean) |
| `witness exist a,b,c,d N+ st {a^4+b^4+c^4=d^4} from …` | 2.094 | 14.718 | **7.03×** | `decide` | [lit](sources/elementary/fourth_power_witness.lit) |
| `gcd(2178309,1346269) = 1` | 0.455 | 0.992 | **2.18×** | `rfl` | [lit](sources/elementary/gcd_2178309.lit) |

素性一例的 Lean 路线用的是 `native_decide`：它在本机编译求值，`#print axioms` 会记录一条生成公理依赖。同一目标用 `norm_num` 需要 718 ms。表里取的是**已测最快**写法，所以这是对 Lean 有利的比较。

### 4. 量词、见证、唯一存在与存在消去（2026-10-23，21 例）

每例都测了 tactic、直接引理与简短证明项多条路线，下表取每题已测最快的 Lean 写法。“语句形状”指这条命题主要考的是哪种 Litex 语句。

| 语句形状 | 数学语句 | Litex | Lean | 倍率 |
| --- | --- | ---: | ---: | ---: |
| 全称 + 加法保号 | 两正实数之和为正 | 0.394 | 9.305 | **23.60×** |
| 全称 + 乘法保号 | 两正实数之积为正 | 0.408 | 4.986 | **12.23×** |
| 全称 + 传递 | 严格不等式的传递性 | 0.256 | 1.240 | **4.84×** |
| 全称 + 不等式平移 | 不等式两边加上同一实数 | 0.469 | 9.537 | **20.33×** |
| 全称 + 幂 | 任意实数的平方非负 | 0.597 | 13.491 | **22.60×** |
| 全称 + 绝对值 | 绝对值三角不等式 | 5.261 | 7.338 | **1.39×** |
| 全称 + 倒数 | 正实数的倒数为正 | 0.287 | 8.167 | **28.43×** |
| 全称 + 除法 | 非零实数除以自身等于一 | 0.387 | 3.301 | **8.52×** |
| 全称 + 反对称 | 双向弱不等式推出相等 | 0.287 | 1.217 | **4.24×** |
| 全称 + 析取结论 | 零乘积推出一个因子为零 | 0.203 | 6.860 | **33.83×** |
| 全称 + 多项式恒等式 | 平方展开式 | 1.589 | 15.006 | **9.44×** |
| 全称 + 实例化 | 把全称函数性质用到 0 上 | 0.675 | 1.238 | **1.83×** |
| 见证 | 实数平方等于四 | 0.512 | 4.789 | **9.36×** |
| ∀∃ 构造 | 对每个实数构造更大的实数 | 1.071 | 1.384 | **1.29×** |
| ∀∃ + 正性 | 给定正数构造更小的正数 | 1.628 | 10.215 | **6.28×** |
| 唯一存在 | 每个实数有唯一加法逆元 | 1.422 | 3.795 | **2.67×** |
| ∀∃ 双约束 | 构造和与差都给定的两个实数 | 3.219 | 21.098 | **6.56×** |
| 存在消去 | 由平方根存在推出非负 | 4.148 | 14.026 | **3.38×** |
| 存在消去 + 换尺度 | 提取平方根后构造四倍数平方根 | 9.502 | 14.557 | **1.53×** |
| ∀∃ + 上界 | 为两个实数构造共同上界 | 1.745 | 1.871 | **1.07×** |
| 非空集合见证 | 用见证证明正实数集合非空 | 0.084 | 6.439 | **76.88×** |

源码在 `sources/quantifiers/`：每例一个 `.lit`，每条 Lean 路线一个 `<id>_<method>.lean`。

这 21 例说明一个规律：**命题里需要的良定义性、作用域和规则越多，Litex 的优势越大**；当 Lean 有专门的一行引理（`lt_trans`、`le_antisymm`、`exists_gt`、`abs_add_le`）时，差距塌到 1–5 倍。

### 5. 定义与证明命令（2026-10-23，10 个程序）

整段程序（定义 + 使用，或完整证明块）的耗时：

| 程序 | Litex | Lean | 倍率 | 源码 |
| --- | ---: | ---: | ---: | --- |
| 表达式函数：定义平方并计算 | 0.730 | 7.609 | **10.42×** | [lit](sources/declarations/expression_function.lit) · [lean](sources/declarations/expression_function.lean) |
| 带定义域条件的倒数函数 | 1.823 | 8.583 | **4.71×** | [lit](sources/declarations/guarded_function.lit) · [lean](sources/declarations/guarded_function.lean) |
| 开区间谓词定义与使用 | 0.189 | 8.223 | **43.45×** | [lit](sources/declarations/predicate.lit) · [lean](sources/declarations/predicate.lean) |
| 按正负分段定义绝对值 | 0.729 | 7.330 | **10.05×** | [lit](sources/declarations/piecewise_function.lit) · [lean](sources/declarations/piecewise_function.lean) |
| 递归定义阶乘并计算 5! | 15.542 | 7.488 | **0.48×** | [lit](sources/declarations/recursive_function.lit) · [lean](sources/declarations/recursive_function.lean) |
| 二维点结构、构造与字段访问 | 0.573 | 7.615 | **13.30×** | [lit](sources/declarations/structure.lit) · [lean](sources/declarations/structure.lean) |
| 定义并调用“正实数非零”定理 | 0.158 | 8.018 | **50.74×** | [lit](sources/declarations/named_theorem.lit) · [lean](sources/declarations/named_theorem.lean) |
| 反证：不存在平方等于 -1 的实数 | 4.127 | 49.472 | **11.99×** | [lit](sources/declarations/contradiction.lit) · [lean](sources/declarations/contradiction.lean) |
| 分类讨论：绝对值等于原数或其相反数 | 0.757 | 10.576 | **13.97×** | [lit](sources/declarations/cases_proof.lit) · [lean](sources/declarations/cases_proof.lean) |
| 归纳证明前 n 个正整数的求和公式 | 43.626 | 174.986 | **4.01×** | [lit](sources/declarations/induction_proof.lit) · [lean](sources/declarations/induction_proof.lean) |

这批还分别测了“只声明定义”和“在已载入定义的新上下文中使用定义”两段，见 `results/selected-cases-2026-10-22-23.csv` 之外的原始记录。

---

## 二、本轮新增：更宽的领域（2026-10-23）

这一轮补的是前五批没覆盖的领域：集合、函数、整数算术与整除、有限组合、微积分，以及一个“稍微大一点”的经典证明。用例定义在 `cases/new-round.json`，源码在 `sources/new-round/`，原始样本在 `results/new-round-raw.json`。

| 领域 | 数学语句 | Litex 写法要点 | Lean 写法要点 | Litex | Lean | 倍率 |
| --- | --- | --- | --- | ---: | ---: | ---: |
| 经典大证明 | √2 不是有理数 | `by contra:` + 唯一既约分数 + 素数整除幂，推出 p、q 同为偶数 | 同五步：`Rat.num`/`Rat.den` 互素 + 奇偶性 + `Nat.Prime.dvd_of_dvd_pow` | 25.554 | 750.544 | **29.37×** |
| 集合 | 并交分配律 | `union(A,intersect(B,D))=intersect(union(A,B),union(A,D))` | `Set.union_inter_distrib_left` | 0.234 | 1.348 | **5.77×** |
| 集合 | 差集对并集的德摩根律 | `set_minus(A,union(B,D))=intersect(set_minus(A,B),set_minus(A,D))` | `ext` + `simp` + `tauto` | 0.221 | 21.592 | **97.48×** |
| 集合 | 交集保持包含 | `A $subset B =>: intersect(A,D) $subset intersect(B,D)` | `Set.inter_subset_inter_left` | 0.286 | 1.355 | **4.73×** |
| 函数 | 函数值属于值域 | `f(x) $in fn_range(f)` | `Set.mem_range_self` | 0.228 | 0.861 | **3.78×** |
| 函数 | 复合的结合律 | `compose(compose(f,g),h)=compose(f,compose(g,h))` | `rfl` | 6.454 | 0.879 | **0.14×** |
| 整数算术 | 整数除法的商余分解 | `a=d*quot(a,d)+a%d` | `Int.mul_ediv_add_emod` | 0.379 | 3.183 | **8.41×** |
| 整除 | 整数乘积被其因子整除 | `$dvd(a*c,c)` | `dvd_mul_left` | 0.204 | 1.719 | **8.42×** |
| 有限组合 | `{1,2,3}` 的元素个数 | `finite_set_size({1,2,3})=3` | `by decide` | 0.062 | 3.754 | **60.91×** |
| 有限组合 | n 元集合有 2ⁿ 个子集 | `finite_set_size(power_set(A))=2^finite_set_size(A)` | `Finset.card_powerset` | 0.165 | 1.083 | **6.56×** |
| 组合 | 自然数阶乘为正 | `factorial(n)>0` | `Nat.factorial_pos` | 0.096 | 0.597 | **6.25×** |
| 微积分 | x² 在 3 处的导数为 6 | `$has_derivative_at(fn(t R) R {t^2},3,6)` | `hasDerivAt_pow` + `congr_deriv` + `norm_num` | 0.850 | 49.035 | **57.67×** |
| 笛卡尔积 | 有序对的坐标重构 | `(p(1),p(2))=p` | `Prod.mk.eta` | 0.195 | 0.608 | **3.12×** |
| 微积分 | x² 在 3 处连续 | `$is_continuous_at(fn(t R) R {t^2},3)` | `continuousAt_pow` | 0.250 | 8.686 | **34.79×** |

同一个命题在 Lean 侧换写法，差别可能很大，所以每条备选路线都单独测了：

| 用例 | Lean 路线 | 写法提要 | Lean (ms) | 倍率 |
| --- | --- | --- | ---: | ---: |
| √2 不是有理数 | `scratch`（主表口径） | 从 `Rat.num`/`Rat.den` 起自己推五步 | 750.544 | **29.37×** |
| √2 不是有理数 | `mathlib_theorem` | 一行引用 `irrational_sqrt_two` | 0.658 | 0.03× |
| 并交分配律 | `lemma`（主表口径） | 引用与目标同形的 `Set.union_inter_distrib_left` | 1.348 | **5.77×** |
| 并交分配律 | `ext_simp` | `ext x` + `simp` + `tauto` 自己拆集合 | 32.526 | 139.28× |
| 交集保持包含 | `lemma`（主表口径） | 引用 `Set.inter_subset_inter_left` | 1.355 | **4.73×** |
| 交集保持包含 | `term` | 直接给出证明项 | 1.962 | 6.85× |
| 复合的结合律 | `lemma` | 引用 `Function.comp_assoc` | 0.879 | **0.14×** |
| 复合的结合律 | `term` | 直接给出证明项 `rfl` | 0.895 | 0.14× |
| `{1,2,3}` 的元素个数 | `decide`（主表口径） | `by decide` | 3.754 | **60.91×** |
| `{1,2,3}` 的元素个数 | `norm_num` | `by norm_num` | 18.637 | 302.42× |
| 有序对的坐标重构 | `lemma`（主表口径） | `Prod.mk.eta` | 0.608 | **3.12×** |
| 有序对的坐标重构 | `term` | 直接给出证明项 | 0.664 | 3.41× |

主表每行标注的路线写在该表的“Lean 最快路线”列里，`results/new-round.md` 也有同样一列。倍率一律用未舍入的中位数计算。

每行都另有完整源码（每条 Lean 路线一个文件）：`sources/new-round/<id>.lit`、`sources/new-round/<id>__<method>.lean`。

### √2 无理数：两侧按同一套步骤做完

两边都做同样五步：反证设 √2 是有理数 → 取唯一既约分数 p/q（gcd(p,q)=1）→ 由 p² = 2q² 得 2 | p²，从而 p 是偶数 → 代回得 q² = 2(p/2)²，从而 q 也是偶数 → 与 gcd(p,q)=1 矛盾。

Litex（25.554 ms）：

```litex
# sqrt(2) is not rational.
by contra:
    ? not sqrt(2) $in Q
    release thm rational_has_unique_reduced_fraction(sqrt(2))
    obtain p, q from exist! p Z, q N+ st {sqrt(2) = p / q, gcd(p, q) = 1}

    p^2 = (sqrt(2) * q)^2 = sqrt(2)^2 * q^2 = 2 * q^2
    p^2 % 2 = (2 * q^2) % 2 = 0
    release thm prime_divides_power(p, 2, 2)

    p / 2 $in Z
    q^2 = p^2 / 2 = 2 * (p / 2)^2
    q^2 % 2 = (2 * (p / 2)^2) % 2 = 0
    release thm prime_divides_power(q, 2, 2)

    impossible 2 <= gcd(p, q) = 1
```

Lean（750.544 ms，[源码](sources/new-round/sqrt_two_irrational__scratch.lean)）：

```lean
import Mathlib

example : Irrational (Real.sqrt 2) := by
  rintro ⟨q, hq⟩
  have h2 : (q : Real) ^ 2 = 2 := by
    rw [hq, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  -- 唯一既约分数：p = |num|, m = den, gcd p m = 1
  set p : Nat := q.num.natAbs with hp
  set m : Nat := q.den with hm
  have hden : (m : Real) ≠ 0 := by
    have : (0 : Nat) < m := q.den_pos
    exact_mod_cast this.ne'
  -- 把 (q : ℝ) = num / den 代入
  have hqeq : (q : Real) = (q.num : Real) / (m : Real) := by
    rw [Rat.cast_def, hm]
  -- p² = 2 m²（先把 ℤ 上的等式转成 ℕ）
  have hnat : p ^ 2 = 2 * m ^ 2 := by
    have hreal : (q.num : Real) ^ 2 = 2 * (m : Real) ^ 2 := by
      rw [hqeq] at h2
      field_simp at h2
      nlinarith [h2]
    have hint : q.num ^ 2 = 2 * (m : Int) ^ 2 := by
      exact_mod_cast hreal
    have habs : ((p : Int)) ^ 2 = 2 * (m : Int) ^ 2 := by
      have hnum : q.num ^ 2 = ((p : Int)) ^ 2 := by
        rcases Int.natAbs_eq q.num with h | h
        · rw [h, hp]
        · rw [h, hp]; ring
      rw [← hnum, hint]
    exact_mod_cast habs
  -- p 是偶数
  have hp2 : 2 ∣ p ^ 2 := ⟨m ^ 2, hnat⟩
  have hp_even : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hp2
  -- 于是 q 也是偶数
  obtain ⟨k, hk⟩ := hp_even
  have hm2 : m ^ 2 = 2 * k ^ 2 := by
    rw [hk] at hnat
    nlinarith
  have hm2dvd : 2 ∣ m ^ 2 := ⟨k ^ 2, hm2⟩
  have hm_even : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hm2dvd
  -- 与 gcd(p, m) = 1 矛盾
  have hcop : p.Coprime m := q.reduced
  have hgcd : 2 ∣ p.gcd m := Nat.dvd_gcd ⟨k, hk⟩ hm_even
  rw [hcop] at hgcd
  omega
```

| Lean 路线 | 做了什么 | Lean (ms) | 倍率 |
| --- | --- | ---: | ---: |
| `scratch`（主表口径） | 与 Litex 相同的五步，从 `Rat.num`/`Rat.den` 起自己推 | 750.544 | **29.37×** |
| `mathlib_theorem` | 一行引用 Mathlib 早已证完的 `irrational_sqrt_two` | 0.658 | 0.03× |

两条路线差三个数量级，正说明“引用一个已经检查过的定理”和“重新检查一遍证明”是完全不同的任务。主表用 `scratch`，因为那才是与 Litex 对等的工作量；`mathlib_theorem` 留在这里只作对照，提醒读者 Lean 侧存在这种一步到位的写法。

需要说明：`scratch` 是本轮从零写出的第一版可编译证明，没有针对速度做过优化（`field_simp`、`nlinarith`、`exact_mod_cast` 都偏重）。熟练的 Lean 用户很可能写出更快的证明；如果之后有优化版本，应当在同一张表里更新，而不是保留这个数字当结论。

### Litex 变慢的地方

两个方向是 Lean 更快：

| 场景 | Litex | Lean | 倍率 | 原因 |
| --- | ---: | ---: | ---: | --- |
| 函数复合结合律 | 6.454 | 0.879 | 0.14× | Lean 的 `rfl` 直接靠定义相等收尾；Litex 要为函数相等构造结构化的验证证据 |
| 递归阶乘 `5!`（用自定义递归函数） | 15.542 | 7.488 | 0.48× | Litex 走从 0 到 5 的显式展开链，每步都留证据；Lean 一次归约 |

这两个方向正好说明：**Litex 的优势来自“命题的形状”和“内置规则”**，不是“所有证明都更快”。凡是“一句话定义相等”的任务，Lean 几乎无法被超过。

但**“引用一个大定理”不能算赢**。√2 那一例，如果 Lean 只写 `irrational_sqrt_two`，数字是 0.658 ms；把两侧都按同一套步骤从零做（本轮已经补上），Lean 是 750.544 ms，Litex 反而快 29 倍。所以本目录的口径是：**比同一件工作，不比谁家现成的定理多**。凡是 Lean 一侧看起来“快得离谱”的用例，都应该先问一句：对面是不是只做了一次引用。

---

## 三、覆盖清单：Litex 的功能被覆盖到哪一步

按 Litex 手册的语句词典（S01–S52）与对象词典（O01–O62）对照，**已经测过**的有：

| Litex 功能 | 覆盖情况 |
| --- | --- |
| 原子事实、合取、析取、链式等式 | 已测（零因子、精确计算链、多项式恒等式） |
| 全称事实、共享假设、`=>:` 作用域 | 已测（量词批 21 例） |
| 存在、见证、唯一存在、存在消去（S35–S38） | 已测（含非空集合见证） |
| 局部 `claim`、`obtain`、释放定理（S25、S33） | 已测（√2、存在消去、命名定理复用） |
| 反证、分情形、归纳（S39、S40、S42） | 已测（各一例） |
| 表达式函数、带定义域函数、分段、递归、按情况（S01、S11、S12、S21、S22） | 已测（定义批 5 例） |
| 具体谓词与 `by def`（S14） | 已测 |
| 结构体与字段访问（S16） | 已测 |
| 命名定理的声明与调用（S18） | 已测 |
| 精确求值与封闭计算（S51） | 已测（算术、对数、阶乘、素性、根式） |
| 集合运算：并、交、差、幂集、包含（O54–O59） | 已测（分配律、德摩根、单调、幂集基数） |
| 函数：值域、复合、向函数本身的全称量化 | 已测 |
| 有限求和、有限集合求和（S44 相关） | 已测（4 种求和） |
| 三角、对数、指数、根式、阶乘、gcd、素性、连续性、导数 | 已测（各 1–3 例） |

**还没有覆盖**、值得下一轮测的：

| 方向 | 为什么值得测 | 预计难点 |
| --- | --- | --- |
| 极限与积分（连续性本轮已覆盖） | 分析是 Litex 原生重点，Mathlib 的分析证明通常很长，是“大例子”的首选 | 本轮试过 `lim(fn(t R) R {t^2},3)=9`：Litex 在良定义阶段就拒绝，必须先给出“3 是实数聚点”和“连续蕴含极限”两步。所以极限只能按整段程序比较，不能当裸语句比 |
| 强归纳、最小反例（S43） | 与普通归纳（4.01×）对照能看出差别 | Litex 的归纳作用域写法需要先确定固定模式 |
| 函数原像、替换像（S09、S10） | 前像/像是 Litex 的独立语句形状 | Lean 侧要选 `Set.image`/`Set.preimage` 的对应写法 |
| 集合外延性、函数外延性（S45、S46） | 会直接对上“自由函数相等”这一 Lean 的强项 | Litex 需要完整的定义域条件，写法较长 |
| 模板声明族、可复用证明策略（S17、S20） | Litex 独有的复用机制，Lean 里对应 `variable`/`macro`/tactic | 对应关系不唯一，得先定“同一任务”的标准 |
| 正则性注册：自反、对称、传递（S48–S50） | 自定义谓词的规则注册，Lean 里对应 `instance`/`simp` 引理 | 需要构造自定义谓词的最小例子 |
| 信任、公理、选择、佐恩引理（S23、S24、S30–S32） | 能对照 Lean 的 `Classical.choice`/`propext` 公理依赖 | 属于信任边界问题，不只是速度 |
| 多文件项目与 `-r` 加载（module_manager） | 真实数学库是分模块的 | 应比较“整库首次检查 + 增量检查”而不是单条语句 |
| `-lean` 编译到 Lean 后的复核 | 这是 Litex 独有路径：生成 Lean 再由 Lean 复核 | 需要把“Litex 检查 + Lean 检查”合并计时 |
| `-extractpython` / `-extractc` | 数值/算法抽取是 Litex 的另一条出口 | 与 Lean 的 `native_decide`、`#eval` 对照 |
| `-latex` 与 reading 模式 | 面向读者/教材，不是检查速度 | 更适合做输出质量对照，而非计时 |
| 不可验证输入的反馈（负例） | 对 AI/交互式工作流同样重要：拒绝一个错误步骤要多久、说清原因要多久 | 需要定义“诊断质量”的指标，不能只比毫秒 |
| 大型定理库（AM-GM、Cauchy–Schwarz、几何库） | 才是“从零建库”的真实负载 | 两边都要从空的数学上下文写起，工作量以小时计 |

一个原则：**只要 Lean 侧能用一行现成引理，Litex 就不会快**；Litex 的优势区间是“命题本身带着定义域、量词和多个推理动作，而 Lean 需要 tactic 或手工证明项去搭”。上表的覆盖清单也是按这个原则挑的。

---

## 四、复现

在仓库根目录：

```sh
cargo build --release
python3 examples/litex_vs_lean_speed/harness/bench.py validate   # 逐条验证两侧源码
python3 examples/litex_vs_lean_speed/harness/bench.py measure    # 计时（约 2–3 分钟）
```

- `validate` 会把每个 Litex 文件交给 release 二进制跑一遍，并把每一条 Lean 路线编进一个 `#print axioms` 文件，确认没有 `sorryAx`。
- `measure` 复用同样源码：Litex 侧编译一个链接 `liblitex.rlib` 的 Rust 计时器（每进程 30 个暖样本、三个进程），Lean 侧用 `#probe`（每进程 7 个暖样本、三个进程）。
- Lean 环境通过 `showcases/litex_to_lean_adapter` 里的 `lake env` 取得 `LEAN_PATH`；没有该适配器项目时可以用 `LEAN_PATH` 环境变量直接指定。
- 换用例：改 `cases/new-round.json`（或传 `--cases`），`validate` 会自动生成 `sources/<名字>/` 下的逐例源码。

## 五、这些数字不能说明什么

- 不是 Litex 与 Lean 的总体速度排名。用例是选录的，样本量、二进制快照和机器负载都不同；五批数据来自不同批次构建的二进制。
- 不是内核归约速度的对照。Lean 侧含证明构造与同步内核检查，Litex 侧含解析、良定义性、验证与证据构建，两侧边界的定义不同。
- 不含用户完成数学任务的时间，也不含编辑器的增量检查、内存占用、启动与导入成本。
- 每条 Lean 路线都取的是**本轮已测**写法，不构成 Lean 可能达到的下界；反过来，Litex 侧也没有为每个命题手写最优证明，它用的是内置规则与策略的默认搜索。
