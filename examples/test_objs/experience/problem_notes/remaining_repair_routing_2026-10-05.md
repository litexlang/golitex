# 剩余记录重新归类与作者修复

Task context：用户要求重审 LEG30 等记录，自行处理局部 `.lit` / Rust / BT 问题，并明确下一阶段工作。活动入口为 [总清单](../../../../plan/src收尾总清单.md)，执行归属为 [修复路线](../../../../plan/剩余问题修复路线_2026-10-05.md)。

## 本轮作者修改

[抽象代数](../../../../showcases/math_concepts_in_litex/6_abstract_algebra/main.lit) 原 `is_ring_homomorphism` 只要求 map 保运算，没有要求两边是环；`is_quotient_ring_presentation` 没有要求 map 是环同态。后续却使用零元律、目标环结构和保乘法。因此补回已有的概念条件：

<!-- litex:skip-test -->
```litex
# 在 is_ring_homomorphism 中：
$is_commutative_ring(A, add_A, zero_A, neg_A, mul_A, one_A)
$is_commutative_ring(B, add_B, zero_B, neg_B, mul_B, one_B)
# 在 is_quotient_ring_presentation 中：
$is_ring_homomorphism(A, add_A, zero_A, neg_A, mul_A, one_A, B, add_B, zero_B, neg_B, mul_B, one_B, map)
```

没有给任意 add_B 添加零元 builtin，原 kernel theorem 数学结论不变。

原 `field_is_integral_domain` 只有 `by def $is_field(...)`，没有证明无零因子。现在对 `x=zero` / `x!=zero` 分情况，从 field 前提取得 inverse_x 并消去：

<!-- litex:skip-test -->
```litex
y=mul(one,y)=mul(mul(inverse_x,x),y)=mul(inverse_x,mul(x,y))=mul(inverse_x,zero)=zero
```

持久 session：补环前缀后的 kernel frame 成功；原剩余 frame 失败；逆元证明 frame 成功；补 quotient 同态前提后有意替换已提交 prefix，源序重放后的剩余 frame 成功。完整输入与失败输出见 journal/回执包。

```sh
target/release/litex -strict -f showcases/math_concepts_in_litex/6_abstract_algebra/main.lit
target/release/litex -strict -r showcases/math_concepts_in_litex/6_abstract_algebra
```

两条 exit0/root success true，文件 **39/39**。真实 import consumer 能 release 整数环定理并验证其限定名 property；同样配置中 `bad_add(x,y)=x+y+1` 声称是环同态拒绝，正确前两项通过、最后目标失败，无 session_error。旧 upstream 保存的是 legacy setting 表面，本轮只改当前公开入口，没有强行覆盖不同版本源码。

[欧氏几何](../../../../showcases/math_concepts_in_litex/2_euclidean_geometry/main.lit) 补两个坐标乘积桥：投影 → 差的平方 → 外层和。真实文件第 5 个根 statement 的一般坐标公式通过。整文件仍 exit1（14/21），第一处新失败为 release 后的 3-4-5 数值断言，后续也未完成；SH02 保持开放，不把独立 prefix 或单个 lemma 当整文件成功。

本轮没有新增 trust、axiom 或 Rust 改动。

## 清理旧分类

当前直接重验：fresh identity 通过，e 参数 parse 拒绝；qualified struct 项目成功；阶乘/lcm 原式和各自持久 tracer 成功。这些共享实现此前已完成，本轮不代领 Rust 修复。

离散数学 10/10、拓扑 16/16、Tarski 93/93 完整文件通过，后两者模块入口成功。旧具体失败删除。SH01/09 本轮各 60 秒未完成，保留已有完整作者成功记录，当前运行时门待定位。

REL05 algo 三项、REL06 原像完整五项成功；前者定义项仍没展示已发布 facts。LEG28 错误枚举正确拒绝，别名 eval 仍拒绝且 Normal 只给泛化阶段；Detailed 对应 catch-all 仍在。后续是局部输出/诊断，不重开 eval 等式存储。

直接 forall-exist 和普通模式源序分条 trust 均通过，DEC01/02 是特定 command/合同边界；旧 operator、example 表面、Point 身份及实指数域另放，不统称数学不能证明。

## 回执范围

[机器 journal](../../proof_journals/remaining_repair_routing_2026-10-05.json) 保存 27 个争议输入、8 个补充文件/模块门、6 个诊断/作者替代、2 个真实 algebra import consumer、SH02 晋升后门及全部 session frames。构建、指纹、完整原文件、失败尝试、stdout/stderr 和 source/binary 在配套 `_receipts.zip`。

root `-r` 的 Normal 汇总 statement_results 为空，所以不将 0 当文件选择数量；同时保存真实非零 `-f` / import 验收。未重跑全部 113 主题、完整 Rust、49 个几何 consumer、全部文档/教材或独立 replay。相邻完整 Rust 933/934 属冻结专项验收，本轮不冒称重跑。

## 记录末共享更新复验

发现10个生产源owner变化后重新构建，最终固定CLI `c37e06113e91a09e500adde57949039e09d171f7da995d6487e08579d116feac`；17个fresh gate期间src/Cargo无漂移，algebra39/39再次通过。LEG41四个原式和8项tracer通过，四个反向错误/非法ln域拒绝。移出待修数学项，不代领共享Rust实施；其它五族原式仍拒。初始源码只有manifest及binary保存，没有完整冻结字节，不把最终src快照冒充初始src；回执明确两个截面。

记录末打包又观察到3个共享exp/ln源码文件变化，已逐名记入journal。ZIP的final-source是打包时工作区快照，不是与最后固定CLI完全匹配的全部源码；固定二进制、输入、前后manifest与完整输出仍保存。以上61个进程的结论属于各自固定gate，不宣称随后HEAD或完整发布已验收。
