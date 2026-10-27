#!/usr/bin/env python3
"""Build an offline explanation from a checked Detailed snapshot and real Lean output.

This is a presentation builder, not a JSON-to-Lean compiler. Canonical compiler
output remains under lean/examples/. An optional --capture directory refreshes
the snapshot from a focused same-result capture and Lean acceptance run.
"""
import argparse
import hashlib
import html
import json
from pathlib import Path
from xml.etree import ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / 'lean/examples/add_zero/statement.lit'
LEAN = SOURCE.with_suffix('.lean')
CORE = ROOT / 'lean/Litex.lean'
SVG = 'http://www.w3.org/2000/svg'
ET.register_namespace('', SVG)
TEAL, ORANGE, INK, GREY = '#007C91', '#C66B32', '#20272B', '#68747B'
SHA = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

LABELS = {
 'en': {
  'title': 'From checked evidence to a Lean proof',
  'subtitle': 'Preserve the source objects, construction conditions and selected proof route.',
  'source': 'Litex source', 'runtime': 'Execute + verify', 'typed': 'Typed results',
  'compiler': 'Replay compiler', 'generated': 'Generated Lean', 'kernel': 'Lean checker',
  'runtime-sub': 'completed Runtime', 'typed-sub': 'WD · rules · citations', 'compiler-sub': 'replay each branch',
  'generated-sub': 'import Litex', 'kernel-sub': 'elaborate → kernel check',
  'json': 'Detailed JSON', 'json-sub': 'inspect the same evidence',
  'resolver': 'Completed Runtime: resolve exact cited IDs',
  'json-note': 'JSON is a view of the results. The current compiler consumes typed results + Runtime.',
  'a': 'Inspect the evidence', 'b': 'Replay the selected route', 'c': 'What Litex.lean supplies',
  'asub': 'Actual source and Detailed fields', 'bsub': 'Recorded evidence → emitted terms', 'csub': 'Lean meaning and proved bridge laws',
  'binder': 'Introduce a complex member', 'binder-sub': 'a ∈ ℂ, stored as f15',
  'construction': 'Check the addition', 'construction-sub': 'a ∈ ℂ and 0 ∈ ℂ certify a + 0',
  'selected': 'Selected equality proof', 'publish': 'Publish the universal fact', 'publish-sub': 'local f1 → quantified f2',
  'map-member': 'Membership citation f15', 'map-construction': 'Addition WD evidence',
  'map-rule': 'Calculation / rational', 'map-fact': 'Stored f1 / exported f2',
  'map-note': 'Fixed normalization inside the selected adapter.',
  'map-note2': 'The final goal does not select a replacement proof.',
  'objects': '1  Objects keep their conditions', 'objects-sub': 'Obj α = value + WD evidence',
  'meaning': '2  Facts have explicit meanings', 'meaning-sub': 'In a A: membership · Same a b: equal denotations',
  'bridges': '3  Bridge laws are proved in Lean', 'bridges-sub': 'native equality + denotation witnesses → Same',
  'interpretation': 'M : Semantics stays explicit.', 'interpretation2': 'The theorem assumes its interpretation laws.',
  'import': 'import Litex provides these declarations and proofs.',
  'foundation': 'Proved library + generated terms → independently checked Lean theorem',
  'native': 'Optional next step: handwritten Adapter → ordinary Lean / Mathlib interface.',
  'boundary': 'This example replays one supported route; JSON import and automatic native interfaces are not implemented here.',
 },
 'zh': {
  'title': '从已验证的证据，到 Lean 证明',
  'subtitle': '保留原始数学对象、构造条件，以及 Litex 实际选中的证明路线。',
  'source': 'Litex 源码', 'runtime': '执行并验证', 'typed': '结构化执行结果',
  'compiler': '证据重放编译器', 'generated': '生成 Lean 代码', 'kernel': 'Lean 检查',
  'runtime-sub': '完成本次 Runtime 执行', 'typed-sub': '良定义 · 规则 · 引用', 'compiler-sub': '重放已记录的分支',
  'generated-sub': 'import Litex', 'kernel-sub': '展开证明项 → 内核检查',
  'json': 'Detailed JSON', 'json-sub': '查看同一份证据',
  'resolver': '已完成的 Runtime：解析被引用的准确事实 ID',
  'json-note': 'JSON 是结果的可读展示；当前编译器直接消费结构化结果与 Runtime。',
  'a': '读出已检查的依据', 'b': '重放选中的证明路线', 'c': 'Litex.lean 提供什么',
  'asub': '真实源码与 Detailed 字段', 'bsub': '已记录的证据 → 实际生成的代码', 'csub': 'Lean 中的数学含义与已证明的桥接',
  'binder': '引入一个复数成员', 'binder-sub': 'a ∈ ℂ，记录为 f15',
  'construction': '检查加法的构造条件', 'construction-sub': 'a ∈ ℂ、0 ∈ ℂ 使 a + 0 合法',
  'selected': '实际选中的等式证明', 'publish': '发布全称事实', 'publish-sub': '局部 f1 → 全称 f2',
  'map-member': '成员关系引用 f15', 'map-construction': '加法的良定义证据',
  'map-rule': 'Calculation / rational', 'map-fact': '存储 f1 / 导出 f2',
  'map-note': '在选中的适配分支内，用固定归一化检查。',
  'map-note2': '编译器沿着记录的路线生成证明。',
  'objects': '1  对象保留构造条件', 'objects-sub': 'Obj α = 对象值 + WD 良定义证据',
  'meaning': '2  给事实明确的数学含义', 'meaning-sub': 'In 表示成员关系；Same 表示含义相等',
  'bridges': '3  桥接规律本身也由 Lean 证明', 'bridges-sub': '数值等式 + 两端的含义证据 → Same',
  'interpretation': '解释参数 M : Semantics 显式保留。', 'interpretation2': '生成定理以该解释满足的规律为条件。',
  'import': 'import Litex 引入这些定义和已证明的规律。',
  'foundation': '已证明的语义库 + 生成的证明项 → Lean 独立检查的定理',
  'native': '可选下一步：手写 Adapter → 普通 Lean / Mathlib 接口。',
  'boundary': '这里展示一条已支持的编译路线；当前没有 JSON 文件导入，也不自动生成普通 Lean 接口。',
 }
}
STYLE = '''
.lean-figure {font-family:Arial,Helvetica,'PingFang SC','Microsoft YaHei',sans-serif;background:white}
.lean-figure text {fill:#20272B;font-size:15px;font-weight:400}
.lean-figure .title {font-size:24px;font-weight:500}
.lean-figure .small {font-size:12.5px;fill:#68747B}
.lean-figure .heading {font-size:16px;font-weight:600}
.lean-figure .letter {font-size:19px;font-weight:700}
.lean-figure .code {font-family:'Courier New',monospace;font-size:13px}
.lean-figure .shape {fill:white;stroke:#A9B4B9;stroke-width:1}
.lean-figure .evidence .shape {fill:#F0F7F8;stroke:#8BB9C0}
.lean-figure .rule .shape {fill:#FCF4ED;stroke:#D7A581}
.lean-figure .arrow {fill:none;stroke:#007C91;stroke-width:1.2}
.lean-figure .view {fill:none;stroke:#8B969C;stroke-width:1;stroke-dasharray:4 3}
.lean-figure .guide {stroke:#CBD2D5;stroke-width:.8}
'''

def el(parent, tag, **attrs):
    return ET.SubElement(parent, f'{{{SVG}}}{tag}', {k.replace('_','-'): str(v) for k,v in attrs.items()})

def text(parent, value, x, y, cls='', anchor='start'):
    e = el(parent, 'text', x=x, y=y, text_anchor=anchor, dominant_baseline='middle', **{'class':cls})
    if cls == 'code': e.set('{http://www.w3.org/XML/1998/namespace}space', 'preserve')
    e.text = value
    return e

def line(parent, d, cls='arrow', marker=True):
    return el(parent, 'path', d=d, **{'class':cls, **({'marker-end':'url(#arrow)'} if marker else {})})

def box(parent, key, x, y, w, h, lines, kind='', step=None):
    g = el(parent, 'g', data_node=key, data_step=step if step is not None else 0, **{'class':f'node {kind}'})
    el(g, 'title').text = lines[0][0]
    el(g, 'rect', x=x, y=y, width=w, height=h, rx=3, **{'class':'shape'})
    for value, dy, cls in lines:
        text(g, value, x+12, y+dy, cls)
    return g

def panel(parent, which, labels):
    text(parent, which, 0, 16, 'letter')
    text(parent, labels[which], 26, 16, 'heading')
    text(parent, labels[f'{which}sub'], 26, 40, 'small')
    if which == 'a':
        box(parent,'source',0,60,352,78,[('forall a C:',24,'code'),('    a + 0 = a',49,'code')],step=0)
        box(parent,'membership',0,160,352,57,[(labels['binder'],18,''),(labels['binder-sub'],40,'small')],'evidence',2)
        box(parent,'construction',0,239,352,57,[(labels['construction'],18,''),(labels['construction-sub'],40,'small')],'evidence',3)
        box(parent,'rule',0,318,352,106,[(labels['selected'],18,''),('"searched_proof": {',43,'code'),('  "type": "builtin_rule",',61,'code'),('  "rule": "Calculation",',79,'code'),('  "mode": "rational" }',97,'code')],'rule',4)
        for a,b in [(138,160),(217,239),(296,318)]: line(parent, f'M 176 {a} V {b-3}')
        text(parent, labels['publish-sub'], 176,447,'small','middle')
    elif which == 'b':
        for key,y,step,title,code in [
            ('map-membership',60,2,labels['map-member'],['h_15 : Litex.In … Litex.C']),
            ('map-construction',151,3,labels['map-construction'],['Litex.add … h_15','  (Litex.numberInC …)']),
            ('map-rule',254,4,labels['map-rule'],['Litex.NativeBridge.','  sameOfDenoteNumber …','  (by ring!)']),
            ('generated',370,5,labels['map-fact'],['have h_1 … / theorem h_2 …'])
        ]:
            h=69 if len(code)==1 else 81 if len(code)==2 else 94
            box(parent,key,0,y,352,h,[(title,19,''), *[(v,43+17*i,'code') for i,v in enumerate(code)]], 'rule' if step==4 else 'evidence',step)
        text(parent, labels['map-note'],0,470,'small')
        text(parent, labels['map-note2'],0,490,'small')
    else:
        box(parent,'objects',0,60,352,94,[(labels['objects'],21,''),(labels['objects-sub'],47,'small'),('Representation M α · denote',72,'code')],'evidence',6)
        box(parent,'meaning',0,178,352,94,[(labels['meaning'],21,''),(labels['meaning-sub'],47,'small'),('Semantics · In · Same',72,'code')],'evidence',6)
        box(parent,'bridges',0,296,352,107,[(labels['bridges'],21,''),(labels['bridges-sub'],48,'small'),('NativeBridge.sameOfDenoteNumber',77,'code')],'rule',6)
        text(parent, labels['interpretation'],0,436,'small')
        text(parent, labels['interpretation2'],0,457,'small')
        text(parent, labels['import'],0,490,'small')

def svg(lang, which=None):
    labels=LABELS[lang]
    width,height=(352,510) if which else (1200,944)
    s=ET.Element(f'{{{SVG}}}svg', {'viewBox':f'0 0 {width} {height}', 'class':'lean-figure', 'role':'img','aria-label':labels[which or 'title']})
    if not which: s.attrib.update(width='183mm',height=f'{183*height/width:.2f}mm')
    el(s,'style').text=STYLE
    defs=el(s,'defs')
    m=el(defs,'marker',id='arrow',viewBox='0 0 7 7',refX=6,refY=3.5,markerWidth=6,markerHeight=6,orient='auto-start-reverse')
    el(m,'path',d='M 0 0 L 7 3.5 L 0 7 Z',fill=TEAL)
    if which:
        panel(s,which,labels)
    else:
        el(s,'rect',width=1200,height=944,fill='white')
        text(s,labels['title'],24,34,'title')
        text(s,labels['subtitle'],24,67,'small')
        items=[('source',24,148,0),('runtime',200,155,1),('typed',383,175,2),('compiler',586,150,5),('generated',764,175,5),('kernel',967,209,7)]
        for key,x,w,step in items:
            lines=[(labels[key],24,'heading')]
            if f'{key}-sub' in labels: lines.append((labels[f'{key}-sub'],49,'small'))
            box(s,f'flow-{key}',x,103,w,70,lines,'evidence' if key in ('typed','generated','kernel') else '',step)
        for (_,x,w,_),(_,nx,_,_) in zip(items,items[1:]): line(s,f'M {x+w} 138 H {nx-5}')
        line(s,'M 471 174 V 201','view')
        box(s,'json',383,207,175,61,[(labels['json'],20,''),(labels['json-sub'],43,'small')],step=2)
        line(s,'M 278 174 V 230 H 366 V 188 H 660 V 176','view')
        text(s,labels['resolver'],680,203,'small')
        text(s,labels['json-note'],24,299,'small')
        el(s,'line',x1=24,y1=323,x2=1176,y2=323,**{'class':'guide'})
        for which,x in [('a',24),('b',424),('c',824)]:
            panel(el(s,'g',transform=f'translate({x} 349)'),which,labels)
        el(s,'line',x1=24,y1=872,x2=1176,y2=872,**{'class':'guide'})
        text(s,labels['foundation'],24,899,'heading')
        text(s,labels['native'],24,925,'small')
    marker_id=f'arrow-{lang}-{which or "full"}'
    return ET.tostring(s,encoding='unicode').replace('id="arrow"',f'id="{marker_id}"').replace('url(#arrow)',f'url(#{marker_id})')

def core_excerpt(start, end):
    source=CORE.read_text()
    return source[source.index(start):source.index(end,source.index(start))].strip()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture',type=Path,help='checked capture with detailed.json and acceptance.json')
    args=parser.parse_args()
    if args.capture:
        evidence=json.loads((args.capture/'acceptance.json').read_text())
        detailed=json.loads((args.capture/'detailed.json').read_text())
        (HERE/'trace.detailed.json').write_bytes((args.capture/'detailed.json').read_bytes())
        (HERE/'evidence.json').write_text(json.dumps(evidence,ensure_ascii=False,indent=2)+'\n')
    evidence=json.loads((HERE/'evidence.json').read_text())
    trace=json.loads((HERE/'trace.detailed.json').read_text())
    assert evidence['detailed_sha256']==SHA(HERE/'trace.detailed.json'), 'Detailed snapshot differs from the checked capture'
    assert evidence['source_sha256']==SHA(SOURCE) and evidence['generated_sha256']==SHA(LEAN)
    assert evidence['core_sha256']==SHA(CORE), 'Refresh the checked snapshot after Core changes'
    assert evidence['lean_kernel_checked'] and evidence['canonical_byte_match']
    fact=trace['statement_results'][0]['verify']['proved_then_facts'][0]['verify_result']
    assert fact['searched_proof']=={'type':'builtin_rule','rule':'Calculation','mode':'rational'}
    assert fact['well_defined']['left']['kind']=='Add'
    assert fact['well_defined']['left']['requirement_fact_verified'][0]['searched_proof']['cite_fact_id']=='f15'
    code=LEAN.read_text()
    assert '(by ring!)' in code and 'sameOfDenoteNumber' in code and 'theorem h_2' in code
    payload={'source':SOURCE.read_text(),'lean':code,'trace':trace,'gate':evidence,
             'core':{
              'object':core_excerpt('structure Obj {','def IsSet {'),
              'add':core_excerpt('def add {','def sub {'),
              'bridge':core_excerpt('theorem sameOfDenoteNumber','/-- Equality eliminates'),
             }}
    template=(HERE/'index.template.html').read_text()
    for lang in LABELS:
        suffix='.zh' if lang=='zh' else ''
        (HERE/f'lean-compilation{suffix}.svg').write_text(svg(lang)+'\n')
        markup=''.join(f'<div class="figure-panel">{svg(lang,p)}</div>' for p in 'abc')
        template=template.replace(f'<!-- FIGURE_{lang.upper()} -->',markup)
    template=template.replace('<!-- DATA -->',json.dumps(payload,ensure_ascii=False).replace('<','\\u003c'))
    (HERE/'index.html').write_text(template)
    acceptance={'evidence':evidence,'boundary':'Detailed JSON is an inspection view; compilation consumes typed results plus completed Runtime. Native Adapter is a separate handwritten step.',
                'assets':{name:SHA(HERE/name) for name in ['index.html','index.template.html','viewer.js','style.css','build.py','export.cjs','README.md','trace.detailed.json','evidence.json','lean-compilation.svg','lean-compilation.zh.svg']}}
    (HERE/'acceptance.json').write_text(json.dumps(acceptance,ensure_ascii=False,indent=2)+'\n')
    print('Built bilingual offline evidence-to-Lean explanation from checked source/output.')

if __name__=='__main__': main()
