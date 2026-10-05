# 对数作者路线：已检原目标 — 2026-10-05

原短式旧过/新拒；本页的全文current通过，全文legacy拒绝。无trust/新增假设；当前CLI84d13156/rlibc34e2cd4。不是已经实施的短规则修复。

## 一般底数乘积

```litex
thm inverse_base_log_bridge:
    ? forall a,u,t R+:
        a!=1
        1<u
        u^(-1)=a
        =>:
            log(a,t)=0-log(u,t)
    u^(-1)!=1
    log(a,t)=log(u^(-1),t)
    log(u^(-1),t)=log(u,t)/(-1)
    log(u,t)/(-1)=0-log(u,t)
claim:
    ? forall a,x,y R+:
        a<1
        =>:
            log(a,x*y)=log(a,x)+log(a,y)
    0<a
    0<1-a
    0<(1-a)/a
    1/a-1=(1-a)/a
    0<1/a-1
    1<1/a
    0<1/a
    have u R+=1/a
    release obj def u
    a!=0
    1/u=1/(1/a)
    1/(1/a)=a
    1<u
    u^(-1)=1/u=a
    a!=1
    release thm inverse_base_log_bridge(a,u,x*y)
    release thm inverse_base_log_bridge(a,u,x)
    release thm inverse_base_log_bridge(a,u,y)
    log(u,x*y)=log(u,x)+log(u,y)
    0-(log(u,x)+log(u,y))=(0-log(u,x))+(0-log(u,y))
    log(a,x*y)=0-log(u,x*y)
    0-log(u,x*y)=0-(log(u,x)+log(u,y))
    (0-log(u,x))+(0-log(u,y))=log(a,x)+log(a,y)
```

## 一般底数反单调

```litex
thm inverse_base_log_bridge:
    ? forall a,u,t R+:
        a!=1
        1<u
        u^(-1)=a
        =>:
            log(a,t)=0-log(u,t)
    u^(-1)!=1
    log(a,t)=log(u^(-1),t)
    log(u^(-1),t)=log(u,t)/(-1)
    log(u,t)/(-1)=0-log(u,t)
claim:
    ? forall a,x,y R+:
        a<1
        x<y
        =>:
            log(a,y)<log(a,x)
    0<a
    0<1-a
    0<(1-a)/a
    1/a-1=(1-a)/a
    0<1/a-1
    1<1/a
    0<1/a
    have u R+=1/a
    release obj def u
    a!=0
    1/u=1/(1/a)
    1/(1/a)=a
    1<u
    u^(-1)=1/u=a
    a!=1
    release thm inverse_base_log_bridge(a,u,x)
    release thm inverse_base_log_bridge(a,u,y)
    log(u,x)<log(u,y)
    0-log(u,y)<0-log(u,x)
```

商/倒数/整数真数幂/两种换底的完整文字及负例、准确来源与publication表见[专项报告](../../../../plan/迁移的plan/legacy-logarithm-audit-2026-10-05.md)及[完整journal](../../../../plan/迁移的plan/proof_journals/legacy-logarithm-audit-2026-10-05.json)。商与倒数实例化需先检查实际R+载体；alias需显式release obj def，不能把遗漏步骤称为内核缺口。任意实指数版本继续归DEC05，不以nZ或对数整数前提版本关闭原问题。
