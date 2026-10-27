'use strict';
(() => {
const data = JSON.parse(document.getElementById('demo-data').textContent);
const $ = id => document.getElementById(id);
const verify = data.trace.statement_results[0].verify;
const equality = verify.proved_then_facts[0].verify_result;
const rows = data.lean.split('\n');
const leanLines = (a, b) => rows.slice(a-1, b).map((line,i) => `${String(a+i).padStart(2)}  ${line}`).join('\n');
const pointer = '/statement_results/0/verify';
const titles = {
 en:['Start with a mathematical fact','Execute and retain the evidence','Keep the original membership citation','Replay the construction conditions','Compile the selected normalization route','Assemble the generated theorem','Give the proof its Lean meaning','Check the generated proof in Lean'],
 zh:['从一个数学事实出发','执行并保留证明证据','保留原始成员关系引用','重放对象的构造条件','编译选中的归一化路线','组装生成的定理','赋予证明明确的 Lean 含义','由 Lean 检查生成的证明']
};
const descriptions = {
 en:[
  'The source says that adding zero leaves every complex object unchanged. We reuse an existing source/generated pair; the displayed Lean is real compiler output.',
  'Runtime verifies the source once and retains ordered typed results, local scopes and cited facts. Detailed JSON displays those results; the compiler also reads the completed Runtime.',
  'Introducing a in C stores its membership as f15 in this run. The addition check cites that exact fact; generated Lean uses h_15. IDs are local to this captured run.',
  'Forming a + 0 requires the recorded child objects and both complex-membership proofs. Litex.add receives h_15 and numberInC 0; a remains a generic certified object.',
  'The actual winner is Calculation / rational. Its adapter emits numeric observations, denotation witnesses, sameOfDenoteNumber and a fixed ring! normalization check.',
  'The compiler preserves local fact f1 as h_1 and exports quantified f2 as h_2. Generic host types, Representation, Obj, membership and M stay explicit.',
  'Litex.lean defines Obj, In and Same and proves the semantic bridges used here. The generated theorem quantifies over interpretations M satisfying the Semantics laws.',
  'Emission and checking are separate. This captured example and current Litex.lean were both freshly checked by pinned Lean 4.31.0/Mathlib. The audit found only standard Lean axioms.'
 ],
 zh:[
  '源码表达：任意复数对象加零后不变。这里复用已有的源码/生成文件对，所展示的 Lean 来自真实编译器输出。',
  'Runtime 执行并验证一次，保留有序的结构化结果、局部作用域和被引用的事实。Detailed JSON 展示这些结果；编译器还会读取已完成的 Runtime。',
  '引入 a ∈ C 时，本次执行把成员关系记为 f15。加法检查引用同一个 f15，生成 Lean 对应使用 h_15。ID 只对这次记录有效。',
  '构造 a + 0 要有已记录的子对象与两个复数成员关系证明。Litex.add 接收 h_15 和 numberInC 0；a 仍是带良定义证据的泛型对象。',
  '实际命中 Calculation / rational 分支。其适配器生成数值观察、含义对应证据、sameOfDenoteNumber，以及固定的 ring! 归一化检查。',
  '编译器把局部事实 f1 保留为 h_1，把全称事实 f2 导出为 h_2。宿主类型、Representation、Obj、成员关系以及解释 M 都显式保留。',
  'Litex.lean 定义 Obj、In、Same，并证明这里用到的语义桥接规律。生成定理对满足 Semantics 规律的解释 M 成立。',
  '生成代码与检查代码是两步。本次例子和当前 Litex.lean 均重新通过固定的 Lean 4.31.0/Mathlib 检查；公理审计只发现 Lean 的标准公理。'
 ]
};
const snippets = [
 [data.source, 'source: lean/examples/add_zero/statement.lit', leanLines(1,10), data.core.object],
 [data.trace, '/', leanLines(1,15), data.core.object],
 [equality.well_defined.left.requirement_fact_verified[0], pointer+'/proved_then_facts/0/verify_result/well_defined/left/requirement_fact_verified/0', leanLines(20,22), data.core.add],
 [equality.well_defined.left, pointer+'/proved_then_facts/0/verify_result/well_defined/left', leanLines(20,22), data.core.add],
 [equality.searched_proof, pointer+'/proved_then_facts/0/verify_result/searched_proof', leanLines(26,31), data.core.bridge],
 [data.trace.statement_results[0].store_and_infer, '/statement_results/0/store_and_infer', leanLines(10,35), data.core.object],
 [equality.searched_proof, pointer+'/proved_then_facts/0/verify_result/searched_proof', leanLines(26,31), data.core.bridge],
 [data.gate, 'evidence.json / focused acceptance', leanLines(10,35), data.core.bridge]
];
const coreLabels = ['Obj · In · Same','Obj · In · Same','Litex.add','Litex.add','NativeBridge.sameOfDenoteNumber','Obj · In · Same','NativeBridge.sameOfDenoteNumber','NativeBridge.sameOfDenoteNumber'];
let lang = new URLSearchParams(location.search).get('lang')==='zh'?'zh':'en';
let step=0, timer=null, selectedNode=null;
const track=$('step-track');
for(let i=0;i<titles.en.length;i++){
 const b=document.createElement('button'); b.type='button'; b.addEventListener('click',()=>{stop();select(i);}); track.appendChild(b);
}
function select(n, nodeKey=null){
 step=Math.max(0,Math.min(titles.en.length-1,n));
 selectedNode=nodeKey;
 $('step-number').textContent=`${String(step+1).padStart(2,'0')} / 08`;
 $('step-title').textContent=titles[lang][step]; $('step-description').textContent=descriptions[lang][step];
 $('inspect-title').textContent=titles[lang][step]; $('inspect-description').textContent=descriptions[lang][step];
 [...track.children].forEach((b,i)=>{b.setAttribute('aria-pressed',String(i===step));b.setAttribute('aria-label',`${i+1}. ${titles[lang][i]}`);b.title=titles[lang][i];});
 document.querySelectorAll('[data-step]').forEach(node=>node.classList.toggle('is-current',Number(node.dataset.step)===step));
 const [json,path,lean,core]=snippets[step];
 $('evidence-pane-title').textContent=step===0?(lang==='zh'?'1 · Litex 源码':'1 · Litex source'):step===7?(lang==='zh'?'1 · 检查记录':'1 · Check receipt'):(lang==='zh'?'1 · Detailed 证据':'1 · Detailed evidence');
 $('json-code').textContent=typeof json==='string'?json:JSON.stringify(json,null,2);
 $('json-path').textContent=path; $('lean-code').textContent=lean; $('core-code').textContent=core;
 $('lean-path').textContent='lean/examples/add_zero/statement.lean · '+(step===4||step===6?'lines 26–31':'actual excerpt');
 $('core-path').textContent=coreLabels[step];
 if(nodeKey==='objects'||nodeKey==='meaning'){
  $('core-code').textContent=data.core.object;
  $('core-path').textContent='Obj · denote · Same · In';
  $('lean-code').textContent=leanLines(7,15);
  $('lean-path').textContent='lean/examples/add_zero/statement.lean · lines 7–15';
  $('inspect-title').textContent=nodeKey==='objects'?(lang==='zh'?'对象与良定义性':'Objects and well-definedness'):(lang==='zh'?'成员关系与相等的含义':'The meaning of membership and equality');
 }
 for(const id of ['json-code','lean-code','core-code']) $(id).scrollTop=0;
 $('previous').disabled=step===0; $('next').disabled=step===titles.en.length-1;
}
function stop(){
 if(timer)clearInterval(timer); timer=null;
 $('play').setAttribute('aria-pressed','false'); $('play').textContent=lang==='zh'?'播放':'Play';
}
function language(next){
 lang=next; document.documentElement.lang=lang==='zh'?'zh-CN':'en';
 document.title=lang==='zh'?'Litex — 从已验证的证据，到 Lean 证明':'Litex — from checked evidence to Lean';
 document.querySelectorAll('[data-en]').forEach(n=>n.textContent=n.dataset[lang]);
 $('figure-en').hidden=lang!=='en'; $('figure-zh').hidden=lang!=='zh';
 $('language-en').setAttribute('aria-pressed',String(lang==='en')); $('language-zh').setAttribute('aria-pressed',String(lang==='zh'));
 for(const ext of ['svg','pdf','png']) $('download-'+ext).href=`lean-compilation${lang==='zh'?'.zh':''}.${ext}`;
 $('play').textContent=timer?(lang==='zh'?'暂停':'Pause'):(lang==='zh'?'播放':'Play');
 document.querySelectorAll('.node').forEach(n=>n.setAttribute('aria-label',titles[lang][Number(n.dataset.step)]));
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
 if(timer){stop();return;} if(step===7)select(0);
 $('play').setAttribute('aria-pressed','true');$('play').textContent=lang==='zh'?'暂停':'Pause';
 timer=setInterval(()=>{if(step===7){stop();return;} select(step+1);},2200);
});
$('language-en').addEventListener('click',()=>language('en')); $('language-zh').addEventListener('click',()=>language('zh'));
$('source-full').textContent=data.source; $('lean-full').textContent=data.lean;
$('verification-record').textContent=JSON.stringify(data.gate,null,2);
document.addEventListener('visibilitychange',()=>{if(document.hidden)stop();});
language(lang);
})();
