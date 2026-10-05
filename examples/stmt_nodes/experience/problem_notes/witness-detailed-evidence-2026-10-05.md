# Witness Detailed evidence repair — 2026-10-05

Atomic witness already verifies the argument, projected existential, ambient
WD, dependent witness types, local proof and body obligations. Detailed used
to discard those successful fields. It now projects their actual owned results,
in execution order. No executor, AST/result layout, Env/Runtime, search ceiling,
mathematical domain or Normal changes. local_env remains intentionally omitted.

```litex
prop atom_body(a R):
    exist x R st {x=a}
witness $atom_body(2) from 2:
    2=2
$atom_body(2)
```

```litex
prop atom_dep(a R):
    exist x R,y {x} st {y=a}
witness $atom_dep(2) from 2,2
$atom_dep(2)
```

The dependent case retains each instantiated type check, including
2 $in {2}; the tests compare actual child projections in English and Chinese.
The nonempty witness failure enum already owns ObjWd, SetWd, ProofBody or
Membership. Detailed now projects exactly that stage and child:

```litex
witness $is_nonempty_set({1}) from 2
```

```litex
witness $is_nonempty_set({1}) from 1:
    1=1
    0=1
```

The local-proof failure is step_index=1, with the actual failed 0=1 statement.
Object/set division-by-zero failures are separately observed. Direct lookup
tests confirm failed nonempty witnesses do not publish, and later failed
attempts preserve a previously valid publication. Ordinary Runtime does not
promise whole-source rollback.

Legacy accepted an invalid supplied function-space witness:

```litex
witness $is_nonempty_set(fn(x R)R) from 0
```

This deliberate removal is excluded from migration. A real function member
passes both versions:

```litex
witness $is_nonempty_set(fn(x R)R) from fn(y R)R{y}
```

The [persistent tracer](../../witness/witness_detailed_evidence.lit) passes
current strict mode. 34 before/after Normal outputs are byte-identical; final
21 distinct focused tests passed (7 family, 9 Detailed, actual 5 binding selector).
102 normal strict-e / 80 Detailed calls, 3 persistent public Runtime sessions /
82 frames, 34 separate typed Runtime metadata calls, 12 strict files (8 accept /
4 observed invalid rejects). Initial warning truncation and compile repair are
retained; full final test stdout/stderr is stored. No full-release/all-language/
Lean/independent-certificate gate claimed. Existing LEG28 eval/enumeration and
LEG29 full owner/replay scope remain open; 113 themes / 32 legacy themes unchanged.

Final frozen CLI 45a90bedd20f6b4e2bf2edb0ea869ffa9449726a5943bed02231641cd356e5b6 / rlib 48f771608b8f68595b3a9ea3980a9ab7df68ea467d4703cd81c865fc17e67409; 661条src/Cargo在构建、probe-end与记录末稳定. See the
[complete audit](../../../../plan/迁移的plan/legacy-witness-evidence-audit-2026-10-05.md)
and [full raw journal](../../../../plan/迁移的plan/proof_journals/legacy-witness-evidence-audit-2026-10-05.json).
