'use strict';
// Actual failed case scopes and checked prefixes, through public reader events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node failed-case-context.cjs <native-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'failed-case-'+name+'.json'),'utf8'));
function records(b){const nodes=new Map(b.evidence_nodes.map(row=>[row.id,row.node]));function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}return {nodes,resolve};}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const view={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,'source row '+line);return row;},async hover(line,focus=false){const row=view.row(line);if(focus)await row.querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>row.querySelector('.lr-source-code');await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await row.querySelector('.lr-source-code').trigger('pointermove');for(let i=0;i<3;i++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card,'hover '+line);return card;},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'presentation leaves all source/native records unchanged');reader.destroy();}};
 assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length,'logical actions add no source rows');return view;
}
const caseAction=(v,line)=>v.row(line).querySelector('[data-logical-kind="case-assumption"]');
async function run(){let checked=0;
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const name of ['body-first','body-after-prefix','canonical-prefix','closing-goal','closing-impossible','body-second','nested-cases','duplicate-conditions','conjunction','chain','source-style','case-scope-failure']){
  const b=fixture(name),d=records(b),v=mount(b,locale,editable),contexts=[...d.nodes.values()].filter(n=>n.type==='ByCasesBranchFailure');assert(contexts.length,name);
  for(const context of contexts){
   const f=context.fields,scope=d.resolve(f.local_env).scope_id,owner=b.scopes.find(s=>s.id===scope)?.statement_id,s=b.statements.find(s=>s.id===owner);assert(s?.status==='rejected');
   const condition=d.resolve(f.assumption);let at=condition;while(at.fields?.['0'])at=d.resolve(at.fields['0']);const line=at.fields?.line_file?.line;assert(line,name+': native case anchor');assert(caseAction(v,line),name+': active case header');
   assert(!v.row(s.line).querySelector('[data-logical-kind="conclusion"]'),'rejected parent publishes no conclusion');
   const card=await v.hover(line,true);assert(card.textContent.includes(locale==='zh'?'本分支内暂设':'within this case'));assert(card.textContent.includes(locale==='zh'?'尚未完成':'unfinished'));const id=d.resolve(f.assumption_fact_id).fact_id;assert(card.querySelectorAll('.lr-fact-link').some(link=>link.dataset.fact===id));
   const failureLink=card.querySelector('.lr-failed-case-link');assert(failureLink);await failureLink.click();assert(v.reader.getSelection().issue);await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().focusLine,line);await v.close();
   const children=b.statements.filter(child=>child.parent_statement_id===s.id&&child.scope_id===scope&&['accepted','rejected'].includes(child.status));
   for(const child of children){const c=await v.hover(child.line);assert(c.querySelectorAll('.lr-proof-context').some(frame=>frame.dataset.scope===scope),name+': actual local context on '+child.line);if(child.status==='accepted')assert(c.querySelector('.lr-proof-evidence'),'checked prefix retains its real proof');await v.close();}
   const header=await v.hover(s.line);assert(header.querySelectorAll('.lr-proof-context').some(frame=>frame.dataset.scope===scope),name+': context on rejected parent header');await v.close();checked++;
  }
  if(name==='nested-cases'){const line=b.statements.find(s=>s.source_text==='2 = 3').line,c=await v.hover(line),frames=c.querySelectorAll('.lr-proof-context');assert.equal(frames.length,2,'outer and inner case conditions retained in order');assert.notEqual(frames[0].dataset.scope,frames[1].dataset.scope);await v.close();}
  if(name==='body-after-prefix'){const suffix=b.statements.find(s=>s.source_text==='4 = 4');assert.equal(suffix.status,'not_exported');assert(!v.row(suffix.line).querySelector('.lr-proof-point,.lr-inference-toggle'));}
  if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-logical-action,.lr-proof-popover,.lr-inference-toggle').length,0,'editing invalidates stale proofs and assumptions');}v.done();
 }
 for(const name of ['coverage-wd','existing-cases-missing']){const b=fixture(name),v=mount(b,'en');assert.equal(v.root.querySelectorAll('[data-logical-kind="case-assumption"]').length,0,'a case not entered receives no assumed facts');v.done();}
 for(const name of ['claim-prefix','scope-recovery']){const b=fixture(name),v=mount(b,'en');for(const s of b.statements.filter(s=>s.status==='rejected'))assert(!v.row(s.line).querySelector('[data-logical-kind="conclusion"]'));v.done();}
 for(const control of ['legacy-source','wrong-index','wrong-stage','foreign-source','wrong-span','wrong-line','wrong-scope','missing-assumption','source-only']){
  const b=fixture('body-first'),d=records(b),s=b.statements.find(s=>s.statement_kind.endsWith('ByCasesStmt')),context=[...d.nodes.values()].find(n=>n.type==='ByCasesBranchFailure'),failure=[...d.nodes.values()].find(n=>n.type==='ExecByCasesStmtFailed'&&n.variant==='Branch'),entry=s.case_contexts[0],line=entry.header.line;
  if(control==='legacy-source')delete s.case_contexts;
  if(control==='wrong-index')failure.fields.index=20;
  if(control==='wrong-stage')d.resolve(context.fields.failure).variant='FutureStage';
  if(control==='foreign-source')entry.header.source_id='foreign';
  if(control==='wrong-span')entry.header.start_byte++;
  if(control==='wrong-line')entry.header.line++;
  if(control==='wrong-scope')context.fields.local_env={kind:'scope',scope_id:'file:source0'};
  if(control==='missing-assumption')delete context.fields.assumed;
  if(control==='source-only')failure.fields.failed={kind:'unavailable'};
  const v=mount(b,'en');assert.equal(!!caseAction(v,line),control==='legacy-source',control+': source syntax alone cannot certify an entered assumption');v.done();checked++;
 }
 console.log(JSON.stringify({passed:true,checked,bilingualEditableAndReadOnly:true,actualFailedScopeAndAssumption:true,checkedPrefixAndUncheckedSuffix:true,nestedFrames:true,headerAndStepNavigation:true,legacyNativeContext:true,missingOrConflictingEvidenceNotGuessed:true,nativeRecordsUnchanged:true,browserObserved:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
