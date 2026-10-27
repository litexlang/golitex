'use strict';
(() => {
const rawData = document.getElementById('demo-data').textContent.trim();
if (rawData === '<!-- DATA -->') {
 const destination = new URL('index.html', location.href);
 destination.search = location.search || '?lang=zh';
 destination.hash = location.hash;
 location.replace(destination.href);
 return;
}
const data = JSON.parse(rawData);
const $ = id => document.getElementById(id);
const verify = data.trace.statement_results[0].verify;
const equality = verify.proved_then_facts[0].verify_result;
const rows = data.lean.split('\n');
const leanLines = (a, b) => rows.slice(a-1, b).map((line,i) => `${String(a+i).padStart(2)}  ${line}`).join('\n');
const pointer = '/statement_results/0/verify';
const details = {
 source:[data.source, 'source: lean/examples/add_zero/statement.lit', leanLines(1,10), data.core.object, 'Obj · In · Same'],
 results:[verify, pointer, leanLines(20,31), data.core.add, 'Litex.add'],
 membership:[equality.well_defined.left.requirement_fact_verified[0], pointer+'/proved_then_facts/0/verify_result/well_defined/left/requirement_fact_verified/0', leanLines(20,22), data.core.add, 'Litex.add'],
 construction:[equality.well_defined.left, pointer+'/proved_then_facts/0/verify_result/well_defined/left', leanLines(20,22), data.core.add, 'Litex.add'],
 normalization:[equality.searched_proof, pointer+'/proved_then_facts/0/verify_result/searched_proof', leanLines(26,31), data.core.bridge, 'NativeBridge.sameOfDenoteNumber'],
 generated:[data.trace.statement_results[0].store_and_infer, '/statement_results/0/store_and_infer', leanLines(1,35), data.core.object, 'Obj · In · Same'],
 objects:[data.trace.statement_results[0].store_and_infer, '/statement_results/0/store_and_infer', leanLines(7,15), data.core.object, 'Obj · denote · Same · In'],
 check:[data.gate, 'evidence.json / focused acceptance', leanLines(10,35), data.core.bridge, 'NativeBridge.sameOfDenoteNumber']
};
// A single stage definition drives the top controls, left overview and node ownership.
const stages = [
 {title:{en:'Source + verification',zh:'Litex 源码与验证'},
  description:{en:'The source says that adding zero leaves every complex object unchanged. Runtime verifies it once and retains ordered results, local scopes and cited facts for compilation.',zh:'源码表达：任意复数对象加零后不变。Runtime 执行并验证一次，保留有序结果、局部作用域和被引用的事实，供后续编译使用。'},
  nodes:['source'],detail:'source'},
 {title:{en:'Typed results',zh:'结构化结果'},
  description:{en:'The results record membership f15, the addition construction conditions and the selected Calculation / rational proof. Detailed JSON displays this evidence; compilation reads the typed results and completed Runtime.',zh:'结构化结果记录成员关系 f15、加法的良定义条件，以及选中的 Calculation / rational 证明。Detailed JSON 展示这些证据；编译器读取结构化结果与已完成的 Runtime。'},
  nodes:['membership','construction','rule'],detail:'results'},
 {title:{en:'Replay compiler',zh:'证据重放编译器'},
  description:{en:'Replay follows the recorded evidence: f15 becomes h_15, addition WD enters Litex.add, and the rational route uses sameOfDenoteNumber with a fixed ring! normalization check.',zh:'编译器按已记录的证据重放：f15 对应 h_15，加法良定义证据进入 Litex.add，有理式路线通过 sameOfDenoteNumber 和固定的 ring! 归一化检查生成证明。'},
  nodes:['map-membership','map-construction','map-rule'],detail:'normalization'},
 {title:{en:'Generated Lean',zh:'生成 Lean 代码'},
  description:{en:'The generated file imports Litex, keeps local f1 as h_1 and exports f2 as h_2. Objects, membership and the interpretation M remain explicit; Litex.lean supplies their meaning and proved bridge laws.',zh:'生成文件通过 import Litex 引入语义与已证明的桥接规律，把局部 f1 保留为 h_1、全称 f2 导出为 h_2，并显式保留对象、成员关系及解释参数 M。'},
  nodes:['generated','objects','meaning','bridges'],detail:'generated'},
 {title:{en:'Lean check',zh:'Lean 检查'},
  description:{en:'Lean checks generated theorem h_2 for the same statement: for every complex a, a + 0 = a. The recorded run checked the generated file and Litex.lean with pinned Lean 4.31.0/Mathlib; the full receipt is below.',zh:'Lean 检查的仍是“任意复数 a，a + 0 = a”对应的生成定理 h_2。记录中的检查已用固定的 Lean 4.31.0/Mathlib 验证生成文件和 Litex.lean；完整记录保留在页面底部。'},
  nodes:[],detail:'check'}
];
const nodeDetails = {
 source:'source',membership:'membership',construction:'construction',rule:'normalization',
 'map-membership':'membership','map-construction':'construction','map-rule':'normalization',
 generated:'generated',objects:'objects',meaning:'objects',bridges:'normalization'
};
const nodeStages = new Map(stages.flatMap((stage,i)=>stage.nodes.map(key=>[key,i])));
const lastStep=stages.length-1;
const leanVersion=/version ([\d.]+)/.exec(data.gate.lean_version)?.[1]||data.gate.lean_version;
const theoremName=/theorem (h_\d+)/.exec(data.lean)?.[1]||'—';
let lang = new URLSearchParams(location.search).get('lang')==='zh'?'zh':'en';
let step=0, timer=null, selectedNode=null;
function checkSummary(){
 const status=value=>lang==='zh'?(value?'通过':'未确认'):(value?'passed':'not confirmed');
 return lang==='zh'?
  `数学命题：∀ a ∈ ℂ, a + 0 = a\n\nLitex 验证：${status(data.gate.source_success)}\n生成定理：${theoremName}\n生成代码与保存文件一致：${status(data.gate.canonical_byte_match)}\nLean 内核检查：${status(data.gate.lean_kernel_checked)}\nLean 版本：${leanVersion}\n\n完整检查记录见页面底部“验证记录”。`:
  `Statement: ∀ a ∈ ℂ, a + 0 = a\n\nLitex verification: ${status(data.gate.source_success)}\nGenerated theorem: ${theoremName}\nGenerated file matches: ${status(data.gate.canonical_byte_match)}\nLean kernel check: ${status(data.gate.lean_kernel_checked)}\nLean version: ${leanVersion}\n\nFull receipt: “Verification record” at the bottom of this page.`;
}
const track=$('step-track');
for(let i=0;i<stages.length;i++){
 const b=document.createElement('button'); b.type='button'; b.addEventListener('click',()=>{stop();select(i);}); track.appendChild(b);
}
document.querySelectorAll('.node[data-node]').forEach(node=>{
 const owner=nodeStages.get(node.dataset.node);
 if(owner===undefined)node.removeAttribute('data-step');
 else node.dataset.step=String(owner);
});
function select(n, nodeKey=null){
 step=Math.max(0,Math.min(lastStep,n));
 selectedNode=nodeKey;
 const current=stages[step];
 $('step-number').textContent=`${String(step+1).padStart(2,'0')} / ${String(stages.length).padStart(2,'0')}`;
 $('step-title').textContent=current.title[lang]; $('step-description').textContent=current.description[lang];
 $('inspect-title').textContent=current.title[lang]; $('inspect-description').textContent=current.description[lang];
 [...track.children].forEach((b,i)=>{b.setAttribute('aria-pressed',String(i===step));b.setAttribute('aria-label',`${i+1}. ${stages[i].title[lang]}`);b.title=stages[i].title[lang];});
 document.querySelectorAll('[data-step]').forEach(node=>node.classList.toggle('is-current',Number(node.dataset.step)===step));
 const detailKey=nodeDetails[nodeKey]||current.detail;
 const [json,path,lean,core,coreLabel]=details[detailKey];
 $('evidence-pane-title').textContent=detailKey==='source'?(lang==='zh'?'1 · Litex 源码':'1 · Litex source'):step===lastStep?(lang==='zh'?'1 · 这个命题的检查结果':'1 · Checks for this statement'):(lang==='zh'?'1 · Detailed 证据':'1 · Detailed evidence');
 $('json-code').textContent=step===lastStep?checkSummary():typeof json==='string'?json:JSON.stringify(json,null,2);
 $('json-path').textContent=step===lastStep?'evidence.json · '+(lang==='zh'?'检查摘要':'check summary'):path;
 $('lean-code').textContent=lean; $('core-code').textContent=core;
 $('lean-path').textContent='lean/examples/add_zero/statement.lean · '+(lang==='zh'?'真实生成片段':'actual excerpt');
 $('core-path').textContent=coreLabel;
 for(const id of ['json-code','lean-code','core-code']) $(id).scrollTop=0;
 $('previous').disabled=step===0; $('next').disabled=step===lastStep;
}
function stop(){
 if(timer)clearInterval(timer); timer=null;
 $('play').setAttribute('aria-pressed','false'); $('play').textContent=lang==='zh'?'播放':'Play';
}
function language(next){
 lang=next; document.documentElement.lang=lang==='zh'?'zh-CN':'en';
 document.title=lang==='zh'?'Litex — 从已验证的证据，到 Lean 证明':'Litex — from checked evidence to Lean';
 document.querySelectorAll('[data-en]').forEach(n=>n.textContent=n.dataset[lang]);
 document.querySelectorAll('.pipeline button strong').forEach((node,i)=>node.textContent=stages[i].title[lang]);
 $('figure-en').hidden=lang!=='en'; $('figure-zh').hidden=lang!=='zh';
 $('semantics-en').hidden=lang!=='en'; $('semantics-zh').hidden=lang!=='zh';
 $('language-en').setAttribute('aria-pressed',String(lang==='en')); $('language-zh').setAttribute('aria-pressed',String(lang==='zh'));
 for(const ext of ['svg','pdf','png']) $('download-'+ext).href=`lean-compilation${lang==='zh'?'.zh':''}.${ext}`;
 $('play').textContent=timer?(lang==='zh'?'暂停':'Pause'):(lang==='zh'?'播放':'Play');
 document.querySelectorAll('.node[data-step]').forEach(n=>n.setAttribute('aria-label',`${stages[Number(n.dataset.step)].title[lang]}: ${n.querySelector('title')?.textContent||''}`));
 const checked=lang==='zh'?(data.gate.lean_kernel_checked?'记录：通过':'记录：未确认'):(data.gate.lean_kernel_checked?'recorded: passed':'recorded: not confirmed');
 document.querySelectorAll('.kernel-check-status').forEach(node=>node.textContent=`${theoremName} · Lean ${leanVersion} · ${checked}`);
 select(step,selectedNode);
}
document.querySelectorAll('[data-step]').forEach(node=>{
 const activate=()=>{stop();select(Number(node.dataset.step),node.dataset.node);};
 node.addEventListener('click',activate);
 if(node.matches('.node')){
  node.setAttribute('role','button');node.setAttribute('tabindex','0');
  node.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();activate();}});
 }
});
$('previous').addEventListener('click',()=>{stop();select(step-1);});
$('next').addEventListener('click',()=>{stop();select(step+1);});
$('play').addEventListener('click',()=>{
 if(timer){stop();return;} if(step===lastStep)select(0);
 $('play').setAttribute('aria-pressed','true');$('play').textContent=lang==='zh'?'暂停':'Pause';
 timer=setInterval(()=>{select(step+1);if(step===lastStep)stop();},2200);
});
$('language-en').addEventListener('click',()=>language('en')); $('language-zh').addEventListener('click',()=>language('zh'));
$('source-full').textContent=data.source; $('lean-full').textContent=data.lean;
const mathematicalSource=data.source.split('\n').filter(line=>!line.trimStart().startsWith('#')).join('\n').trim();
$('example-source').textContent=mathematicalSource; $('trace-source').textContent=mathematicalSource;
$('verification-record').textContent=JSON.stringify(data.gate,null,2);
document.addEventListener('visibilitychange',()=>{if(document.hidden)stop();});
language(lang);
})();
