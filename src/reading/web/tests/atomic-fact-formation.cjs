'use strict';
// Actual atomic formation failures and precise pre-entry goal anchors.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw Error('Usage: node atomic-fact-formation.cjs <fixtures>');
const code=fs.readFileSync(process.env.LITEX_READER_JS||path.join(__dirname,'../reader.js'),'utf8');
const read=name=>JSON.parse(fs.readFileSync(path.join(directory,'atomic-'+name+'.json'),'utf8'));
function records(bundle){const nodes=new Map(bundle.evidence_nodes.map(x=>[x.id,x.node]));function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}function result(v){let n=resolve(v);while(n.fields?.['0'])n=resolve(n.fields['0']);return n;}return{nodes,resolve,result};}
function mount(bundle,locale,editable){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,console,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 return{...dom,root,reader,async hover(line,target){const row=root.querySelector('[data-line="'+line+'"]');assert(row);target=target||row.querySelector('.lr-source-code');if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card);return card;},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'source, IDs, scopes and Native evidence remain unchanged');reader.destroy();}};
}
async function open(node){assert(node);await node.querySelector('summary').click();}
const failures={
 'equal-zero-denominator':[1,'0 ≠ 0'], 'sqrt-negative':[1,'0 ≤ -1'],
 'order-outside-domain':[1,'{1} ∈ R'], 'order-second-domain':[1,'{2} ∈ R'],
 'predicate-arity':[4,'Arity'], 'unknown-predicate':[1,'Undefined'],
 'claim-equal-goal':[2,'0 ≠ 0'], 'contra-equal-goal':[2,'0 ≠ 0'],
 'claim-equal-body':[3,'0 ≠ 0'], 'contra-equal-body':[3,'0 ≠ 0'],
 'claim-member-goal':[2,'0 ≤ -1'], 'claim-order-goal':[2,'{1} ∈ R'],
 'claim-or-goal':[2,'0 ≠ 0'], 'claim-and-goal':[2,'0 ≠ 0'],
 'claim-chain-goal':[2,'0 ≠ 0'], 'contra-or-goal':[2,'0 ≠ 0'],
 'forall-equal-body':[4,'(atomic_x - 1) ≠ 0'],
 'nested-goal-unicode':[5,'0 ≤ -1'], 'nested-goal-comment':[5,'0 ≤ -1'],
 'nested-body-comment':[6,'0 ≠ 0']
};
async function run(){let checked=0;
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const[name,[line,condition]]of Object.entries(failures)){
  const b=read(name),view=mount(b,locale,editable),source=b.sources[0],rows=view.root.querySelectorAll('.lr-code-row'),card=await view.hover(line),tail=card.querySelector('.lr-atomic-wd');
  assert.equal(rows.length,source.content.split('\n').length,'every original source row is retained');
  assert(tail&&!tail.open,name+': failed WD has a closed disclosure');assert.equal(tail.parentNode.children.at(-1),tail);assert(!card.textContent.includes(condition),'failed WD conditions are absent from the main proof');await open(tail);
  if(['Arity','Undefined'].includes(condition)){const signature=tail.querySelector('.lr-wd-signature-failure');assert(signature);assert.equal(signature.dataset.stage,condition);assert(signature.textContent.includes(condition==='Arity'?'singleton_member':'reading_unknown_predicate'));if(condition==='Arity')assert(signature.textContent.includes('1')&&signature.textContent.includes('2'));}
  else{const failed=tail.querySelector('.lr-wd-unproved-conditions');assert(failed,name+': '+tail.textContent);assert(failed.textContent.replaceAll('(-1)','-1').includes(condition),name+': '+failed.textContent);}
  assert(!tail.textContent.includes(locale==='zh'?'未完整导出':'not fully exported'),name+': '+tail.textContent);
  assert.equal(view.root.querySelectorAll('.lr-code-row').length,rows.length,'annotations add no source rows');assert(!/f\d+::/.test(card.textContent));
  const exact=view.root.querySelector('[data-line="'+line+'"]');assert(exact.classList.contains('lr-rejected'),name+': the retained failing row is marked');
  if(name.includes('goal'))assert(!view.root.querySelector('[data-logical-kind="contra-assumption"]'),'failed formation introduces no reverse assumption');
  for(const s of b.statements.filter(s=>s.status==='rejected')){assert.equal(s.produced_fact_ids.length,0);assert.equal(s.inferred_fact_ids.length,0);}
  if(name==='order-second-domain'){const completed=tail.querySelector('.lr-proof-step');assert(completed&&completed.textContent.includes('1 ∈ R'),'the successful first domain check is retained separately');}
  await card.querySelector('.lr-proof-pin').click();assert.equal(view.reader.getSelection().source,source.id);assert.equal(view.reader.getSelection().focusLine,line);await view.close();
  const owner=b.statements.findLast(s=>s.status==='rejected'&&s.line<line);
  if(owner&&name.includes('goal')){const headerCard=await view.hover(owner.line),header=headerCard.querySelector('.lr-failed-statement-header');assert(header);assert(view.root.querySelector('[data-line="'+owner.line+'"]').classList.contains('lr-incomplete-statement'));const link=header.querySelector('.lr-failed-header-link');assert(link);await headerCard.querySelector('.lr-proof-pin').click();await view.root.querySelector('.lr-detail-body .lr-failed-header-link').click();assert.equal(view.reader.getSelection().focusLine,line);await view.root.querySelector('.lr-back').click();assert.equal(view.reader.getSelection().focusLine,owner.line);await view.close();}
  if(editable){const input=view.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!view.root.querySelector('.lr-proof-popover,.lr-diagnostic-point'));}view.done();checked++;
 }
 for(const name of ['predicate-domain','truth-search-failure','claim-truth-failure','malformed-syntax'])for(const locale of ['zh','en']){
  const b=read(name),view=mount(b,locale,true),line=name==='predicate-domain'?4:name==='claim-truth-failure'?1:1,card=await view.hover(line);assert(!card.querySelector('.lr-wd-unproved-conditions,.lr-wd-signature-failure'),'truth or parse failure is not relabelled as failed WD');const tail=card.querySelector('.lr-atomic-wd');if(tail){await open(tail);assert(!tail.querySelector('.lr-wd-unproved-conditions,.lr-wd-signature-failure'));}view.done();checked++;
 }
 for(const name of ['equal-repair','sqrt-repair','order-repair','predicate-repair','claim-equal-goal-repair','claim-equal-body-repair','contra-equal-body-repair','forall-equal-repair','order-second-repair'])for(const locale of ['zh','en']){
  const b=read(name),view=mount(b,locale,true);assert.equal(b.run_result,'success');assert(!view.root.querySelector('.lr-rejected'));const statement=b.statements.findLast(s=>s.status==='accepted'&&!s.parent_statement_id);const card=await view.hover(statement.line);assert(!card.querySelector('.lr-wd-unproved-conditions,.lr-wd-signature-failure'));view.done();checked++;
 }
 for(const control of ['goal-id','scope','source','missing-result','signature-name','signature-actual','argument-object','domain-result','missing-domain-prefix']){
  const name=control.startsWith('signature')||control==='argument-object'?'predicate-arity':control.startsWith('domain')||control==='missing-domain-prefix'?'order-second-domain':'equal-zero-denominator',b=read(name),d=records(b),statement=b.statements.find(s=>s.status==='rejected'),leaf=[...d.nodes.values()].find(n=>['FailToVerifyAtomicFactWellDefinedResult','FailToVerifyEqualFactWellDefinedResult'].includes(n.type)),goal=d.result(leaf.fields.fact);
  if(control==='goal-id')statement.mathematics.subject_fact_id='foreign';if(control==='scope')statement.scope_id='foreign';if(control==='source')goal.fields.line_file.source_id='foreign';
  if(control==='missing-result'){const requirement=[...d.nodes.values()].find(n=>n.type==='FailToVerifyObjWellDefinedByDefCommon'&&n.variant==='Requirement');delete requirement.fields.result;}
  if(control==='signature-name')d.resolve(leaf.fields.reason).fields.predicate={kind:'symbol_reference',symbol_id:'foreign',name:'foreign'};
  if(control==='signature-actual')d.resolve(leaf.fields.reason).fields.actual='1';
  if(control==='argument-object')d.result(leaf.fields.well_defined_of_each_parameter[0]).fields.obj=goal.fields.body[1];
  if(control==='domain-result')d.result(leaf.fields.result).fields.fact=leaf.fields.fact;
  if(control==='missing-domain-prefix')delete leaf.fields.completed;
  const view=mount(b,'en',false),card=await view.hover(statement.line),tail=card.querySelector('.lr-atomic-wd');assert(tail);await open(tail);assert(!tail.querySelector('.lr-wd-unproved-conditions,.lr-wd-signature-failure'));assert(tail.textContent.includes('not fully exported'));view.done();checked++;
 }
 console.log(JSON.stringify({passed:true,checked,bilingualEditableReadOnly:true,atomicEqualityArgumentSignatureAndBuiltinDomain:true,truthAndParsingRemainDistinct:true,precisePreEntryGoalRows:true,UnicodeNestedSources:true,sourceAndBack:true,closedFinalWD:true,retainedDomainPrefix:true,missingForeignRecordsNotGuessed:true,editInvalidation:true,nativeUnchanged:true,browserObserved:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
