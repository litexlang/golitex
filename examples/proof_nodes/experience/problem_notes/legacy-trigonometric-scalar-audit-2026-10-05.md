# 三角函数迁移：连续等式链与 WD 前置 — 2026-10-05

Task：用户要求比较 legacy/current 并汇报值得搬的小功能。冻结 current fd51c2f3/e36ea508；本轮未改 core。诊断与建议不算修复。

原短式旧过／新拒：

```litex
forall x R:
    cos(2*x)=cos(x)^2-sin(x)^2
```
```litex
forall x R:
    cos(pi/2-x)=sin(x)
```

第一轮分散等式不能自动接上最终目标；实际完整源以下两版过：

```litex
claim:
    ?forall x R:
        cos(2*x)=cos(x)^2-sin(x)^2
    2*x=x+x
    cos(2*x)=cos(x+x)
    cos(x+x)=cos(x)*cos(x)-sin(x)*sin(x)
    cos(x)*cos(x)-sin(x)*sin(x)=cos(x)^2-sin(x)^2
    cos(2*x)=cos(x+x)=cos(x)*cos(x)-sin(x)*sin(x)=cos(x)^2-sin(x)^2
forall x R:
    cos(2*x)=cos(x)^2-sin(x)^2
```
```litex
claim:
    ?forall x R:
        cos(pi/2-x)=sin(x)
    cos(pi/2)=0
    sin(pi/2)=1
    cos(pi/2-x)=cos(pi/2)*cos(x)+sin(pi/2)*sin(x)=0*cos(x)+1*sin(x)=sin(x)
forall x R:
    cos(pi/2-x)=sin(x)
```

cosine 另两种平方形状与 sine cofunction 完整原目标也两版通过；不要把短 discovery miss 当全部 checkability 缺失。

tan/cot 首象限 WD：原 goal 的 claim WD 在 body 之前，改成先证非零。下面完整源 current 成功；legacy 因 -pi/2<0 的查证失败而拒绝：

```litex
claim:
    ?forall x R:
        0<x
        x<pi/2
        =>:
            cos(x)!=0
    pi>0
    pi/2>0
    -pi/2<0
    -pi/2<x
    cos(x)!=0
forall x R:
    0<x
    x<pi/2
    =>:
        cos(x)!=0
forall x R:
    0<x
    x<pi/2
    =>:
        tan(x) $in R
```

cot 对应完整源两版过。已证明 WD 不保证正号；原区间 sign 及给显式非零的 sign 仍失败，归 LEG35，不用这些方便路线遮掉实际 missing rule。sin/cos 端点、错倍角/余角、保留真链却给假目标均拒绝。保留完整第一轮失败、第二轮 success、public Runtime 源序结果。

本轮72不同源/144paired strict-e、72Detailed、3Runtime69帧、10文件门；660 src/Cargo 指纹稳定。作者便利 AU55–57，与尚未实施 LEG35–37 分开。所有完整原例和源 owner：[报告](../../../../plan/迁移的plan/legacy-trigonometry-audit-2026-10-05.md)；全部逐字 raw：[journal](../../../../plan/迁移的plan/proof_journals/legacy-trigonometry-audit-2026-10-05.json)。范围不含全系统、Lean、模块或独立 replay。
