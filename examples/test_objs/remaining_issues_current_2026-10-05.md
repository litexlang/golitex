# 剩余问题：当前分类与下一步

Task context：用户要求汇报前实跑、已解项从具体纠错记录删除；本轮进一步要求自行修局部问题，并区分 `.lit`、局部 Rust、BT 和合同工作。

**旧“25张开放卡”是84d13156历史截面，不能继续当当前失败数。** 活动状态在[总清单](../../plan/src收尾总清单.md)，完整原式、owner、执行顺序和验收在[下一阶段路线](../../plan/剩余问题修复路线_2026-10-05.md)。本轮经验 (historical task record; retired)和journal (historical task record; retired)记录真实范围；未宣称全113卡再次验收。

## 当前实际修复项

| 归属 | 卡 | 当前观察 | 下一步 |
| --- | --- | --- | --- |
| 对应 `.lit` | SH02 | 一般坐标公式已通过；release后的 `distance_sq((0,0),(3,4))=(3-0)^2+(4-0)^2` 仍 search miss；整文件14/21 | 补实际发布的 tuple 投影/数值桥，推进后续原证明。 |
| `.lit` / 接口诊断 | EX13 | symbolic_tuple旧构造只剩注释，真实文件parse undefined name | 找现有符号维数tuple构造，不换固定维数或普通function冒充tuple。 |
| 局部数学BT | LEG35/36 | 三角区间符号、区间保序沿用原记录，待独立复验 | 改对应order/equality叶，保留区间和分母非零；完整原式见路线。 |
| 局部数学BT | LEG42 | 合法域exp/ln固定底数桥原式仍search miss | exp R、ln R+、整数指数桥分开，不扩大一般实指数域。 |
| 局部matcher/BT | LEG45 | 给b,d非零后 `a/(b*d)=c` 推 `a=c*(b*d)` 仍search miss | 定位division conversion来源匹配，保留实际source FactId和WD。 |
| JSON输出 | REL05/06 | algo定义/后续使用、原像完整前缀都成功；发布/来源展示仍缺 | 投影已有typed证据，不再称不能运行。 |
| JSON诊断 | LEG28 | 错误枚举正确拒绝；别名eval当前拒绝，仅展示笼统阶段 | 补真实失败payload，再依据原因决定callable是否有局部路由缺陷。 |

已解LEG27/30、LEG39/40，记录末LEG41原目标已过，SH03/08/12及本轮修好的SH05具体纠错段落已删除，解法/回执保存在经验和原专项记录。

## 另列工作

- **性能/完整验收**：REL02/04真实collector、LEG29实际分支及独立replay、GEO01共享producer→consumer。几何以前44个超时本轮未重跑，不能作为当前44个数学失败。SH01/09本轮各60秒未完成JSON；当前运行时门待定位，保留已有完整作者成功证据。
- **已有作者路线**：AUTH/AU、GEO02等便利候选不计作必修问题，不要求所有等价式一句话自动搜出。
- **数学证明债**：EX07有8处trust，SH13的problem207第(1)/(3)问尚未形式化；前者普通模式可跑、strict拒绝trust正确，不算8个执行bug。
- **合同范围**：DEC01嵌套量词反证表示、DEC02 trust-body WD顺序、DEC03/EX09已移除表面、DEC05非整数/实指数域。直接forall-exist与源序分条trust替代本轮已通过，不把这些全部认作健全性缺陷。
- **用户排除**：M05整书推广暂缓、SYS01持续开发，沿用原范围。

## 本轮验收

release SHA256：`dddc1902feee4bbdfd163994ed84aef4867ea447041184f680d1d24b87f55b8d`。初始27个输入/入口期间src/Cargo指纹无漂移；随后作者修改仅两份`.lit`。抽象代数**39/39**、模块和限定名调用者通过，错误环同态输入拒绝。欧氏几何一般坐标lemma通过，完整文件仍开放。

DEC04已按用户确认修正旧负例：原表达式作为正例保留，真实字段载体/错值反例补齐；最新完整Rust库955/955、integration1/1、相邻7/7通过。当前验收 (historical task record; retired)。下方933/934保留为此前冻结截面，不代表当前失败。

同时核验JSON、session_error和exit，超时单列。root `-r` Normal汇总没有逐文件statement列表，不拿其0项当实际选择数。本轮未重跑完整Rust或发布门；相邻933/934及唯一DEC04断言仍是另一冻结验收。

记录末共享exp/ln顺序叶已接入，另行构建固定release `c37e06113e91a09e500adde57949039e09d171f7da995d6487e08579d116feac`，17个定向gate期间src/Cargo稳定。四个LEG41原式和8项tracer过，四个错误顺序/域控制拒绝，algebra仍39/39；LEG35/36/37/42/45仍拒。初始44与后续17进程分别记录，不冒充全库重扫。

记录末打包又观察到3个共享exp/ln源码文件变化，已逐名记入journal。ZIP的final-source是打包时工作区快照，不是与最后固定CLI完全匹配的全部源码；固定二进制、输入、前后manifest与完整输出仍保存。以上61个进程的结论属于各自固定gate，不宣称随后HEAD或完整发布已验收。

LEG37's two original guarded quotient formulas now pass, with symmetric equality,
missing-guard/wrong-argument controls and ten-language actual-leaf consumers.
The scoped definition-rule acceptance (historical task record; retired)
records 27 focused Rust tests and 12 strict whole-file gates. Earlier frozen
binary observations above retain their historical meaning.
