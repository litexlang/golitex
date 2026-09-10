import fs from 'node:fs/promises';
import path from 'node:path';
import { FileBlob, PresentationFile } from '@oai/artifact-tool';

const src='scripts/Litex_BP_2026-08_v25_副本.pptx';
const out='scripts/revised/Litex_可信推理语言_v3.pptx';
const p=await PresentationFile.importPptx(await FileBlob.load(src));
const replace={
 'Litex：\n从AI for Math出发，\n构建AI推理的新一代基础设施':'Litex：\n连接人、AI 与可信知识的形式化语言',
 '自然语言无法进行完备的形式化验证':'自然语言可以表达意图，但无法保证关键推理正确',
 'Lean：连接数学与计算机，但是使用门槛极高，且不可解释。':'Lean 证明了机器可以检查复杂推理，但专业门槛仍然很高',
 'Litex：做更符合AI和人类直觉的推理基础设施（再斟酌一下）':'Litex 用简单、清晰、可验证的语法连接人、AI 与可信知识',
 'Litex： 面向所有人的形式化验证工具':'Litex：连接人、AI 与可信知识的形式化语言',
 '新一代人机可信推理框架':'人和 AI 共同使用的可信推理语言',
 '数学 +AI+ 工程化 = 行业独有的 AI4Math 基础设施':'形式化语言 + AI + 验证，连接人和可信知识',
 '数学+AI+工程化 = 行业独有的AI4Math基础设施':'形式化语言 + AI + 验证，连接人和可信知识',
 'Litex填补了国内AI4Math底层编译基础设施的空白':'Litex 从数学形式化出发，走向跨行业可信推理',
 'Litex 填补了国内 AI4Math 底层编译基础设施的空白':'Litex 从数学形式化出发，走向跨行业可信推理',
 'AI刺激存量需求持续释放，并创造新的需求增长':'AI 生成内容越多，越需要可检查、可追溯的推理',
 '先服务数学家与形式化团队':'从数学形式化切入，扩展到 AI 安全、金融、软件工程与科学',
 '非 Lean 用户扩张':'领域专家扩张',
 '教育 · 量化 · AI4Science · 可信 AI':'AI 安全 · 金融 · 软件工程 · 物理化学',
 'Litex，像CUDA一样的语言+工具生态':'Litex：一门语言，以及围绕它形成的验证工具生态',
 '我们的路径，是已被验证的更优解决方案':'从 AI for Math 到跨行业可信推理',
 '结构约束强度/抽象程度':'表达门槛 / 验证能力',
 'AI可生成性/验证可追溯性':'AI 可生成性 / 推理可追溯性',
 '生态兼容 Lean 用户，将形式化语言推理交给所有人':'让形式化语言推理进入更多专业工作流',
 'Litex内核工程化重构，正式开放生态':'Litex 语言、编译器与验证生态持续演进',
 '首次验证Litex语言原型':'完成 Litex 语言原型与验证闭环',
 '进一步完善推理基础设施基线':'完善编译、反馈与 Lean 兼容基线',
 '完成首批真实业务场景验证订单':'完成首批 AI 安全、金融或软件场景验证',
 '形成可复制的交付品':'形成可复制的语言与工具交付品',
 '谢谢！期待共同推进属于 Litex 的AI推理新基建！':'形式化不应只属于数学家。\nLitex 让人和 AI 都能表达、检查并复用可信知识。'
};
for (const s of p.slides.items) for (const sh of s.shapes.items) {
  if (!sh.text) continue;
  let t=''; try{t=sh.text.text??''}catch{}
  if(!t) continue;
  for(const [a,b] of Object.entries(replace)) if(t===a) { try{sh.text.replace(a,b)}catch{} }
}
// Cover slide 9 with an editable, readable positioning map.
const s=p.slides.items[8];
const bg=s.shapes.add({geometry:'rectangle',position:{left:55,top:125,width:1170,height:505},fill:'#FFFFFF',line:{fill:'#FFFFFF',width:0}});
const title=s.shapes.add({geometry:'textbox',position:{left:75,top:140,width:1120,height:46},fill:'none',line:{fill:'none',width:0}});
title.text='从 AI for Math 到跨行业可信推理'; title.text.style={fontSize:30,bold:true,color:'#111827',typeface:'Arial'};
const body=s.shapes.add({geometry:'textbox',position:{left:85,top:205,width:1100,height:380},fill:'none',line:{fill:'none',width:0}});
body.text='Axiom / Verified AI（AI for Math）\n自动生成并验证数学证明，代表形式化推理的严格起点\n\nJulia（科学计算）\n把数学表达、科学建模与高性能执行放进同一套语言生态\n\nMojo（高性能编程）\n让更多开发者使用接近底层的 AI 与系统能力\n\nCUDA（通用计算基础设施）\n把 GPU 能力变成语言、编译器、运行时与库的完整生态\n\nPramaana Labs（现实世界验证）\n把税务、法律、医疗、软件等领域规则变成可检查的验证系统\n\nLitex（可信推理语言）\n用低门槛形式化语言连接人、AI 与可信知识';
body.text.style={fontSize:18,color:'#1F2937',typeface:'Arial'};
const note=s.speakerNotes?.textFrame; if(note) note.setText('Pramaana Labs public positioning: https://pramaanalabs.ai/');
await (await PresentationFile.exportPptx(p)).save(out);
console.log(out);
