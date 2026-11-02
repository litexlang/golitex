'use strict';
// Native stages and their scopes, through the public source reader events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node proof-processes.cjs <process-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'process-'+name+'.json'),'utf8'));
function records(bundle){
 const nodes=new Map(bundle.evidence_nodes.map(row=>[row.id,row.node]));
 function resolve(value){const seen=new Set();while(value?.kind==='evidence_reference'&&!seen.has(value.evidence_id)){seen.add(value.evidence_id);value=nodes.get(value.evidence_id);}return value||{};}
 function result(value){let node=resolve(value);while(node.fields?.['0'])node=resolve(node.fields['0']);return node;}
 return {nodes,resolve,result};
}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const view={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,line);return row;},
  async hover(line,focus=false){const row=view.row(line);if(focus)await row.querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>row.querySelector('.lr-source-code');await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await row.querySelector('.lr-source-code').trigger('pointermove');for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card,'proof preview at '+line);return card;},
  async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'source and native proof identities remain unchanged');reader.destroy();}};
 assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length,'actions add no source rows');return view;
}
const note=(view,line,kind)=>view.row(line).querySelector('[data-logical-kind="'+kind+'"]');
function firstStatement(bundle,leaf){return bundle.statements.find(s=>s.statement_kind?.split('.').at(-1)===leaf&&s.status==='accepted');}
async function expandRequirements(target){for(const step of target.querySelectorAll('.lr-proof-step')){await step.querySelector('summary').click();assert(!step.textContent.includes('cannot be matched exactly'),step.textContent);}}
async function run(){
 let checks=0;
 for(const locale of ['zh','en'])for(const editable of [true,false]){
  const bundle=fixture('induction'),data=records(bundle),view=mount(bundle,locale,editable),statement=bundle.statements.find(s=>array(s.block_anchors).length),record=data.result(statement.evidence),body=data.resolve(record.fields.body);
  assert(statement,'current native producer must retain structured title positions');
  assert(note(view,statement.line,'conclusion'),'the universal conclusion is published at its producer header');
  const stages=[];
  for(const phase of ['base','step']){
   const stage=data.resolve(body.fields[phase]),scope=data.resolve(stage.fields.local_env).scope_id,anchor=statement.block_anchors.find(a=>a.role==='induction_'+phase),action=note(view,anchor.line,'induction-'+phase);assert(action,'phase at exact native source title');
   const card=await view.hover(anchor.line,phase==='base'),frame=card.querySelector('.lr-process-frame');assert(frame);assert.equal(frame.dataset.scope,scope);assert.equal(frame.dataset.process,'induction-'+phase);
   assert.deepEqual(frame.querySelectorAll('.lr-proof-step').map(step=>step.querySelector('summary').textContent),stage.fields.goals_verified.map(p=>{const f=data.resolve(data.result(p).fields.fact);return f.text.replaceAll('>=','≥').replaceAll('<=','≤');}),'each phase displays its own instantiated goals');
   if(phase==='base')assert(frame.textContent.includes(locale==='zh'?'没有归纳假设':'no induction hypothesis'));
   const ids=frame.querySelectorAll('.lr-proof-grounds .lr-fact-link').map(link=>link.dataset.fact);assert(ids.length>=2);stages.push({scope,ids});await expandRequirements(frame);await view.close();checks++;
  }
  assert(stages[0].ids.every(id=>!stages[1].ids.includes(id)),'base and step assumption identities remain separate');
  const goalLine=bundle.sources[0].content.split('\n').findIndex((line,index)=>index>=statement.line&&line.trim()==='? 2^k >= k + 1')+1;
  assert(note(view,goalLine,'induction-goal'));assert(!view.row(goalLine).dataset.proofFacts,'an induction goal is not a globally established fact or a flat mix of case assumptions');
  let card=await view.hover(statement.line);assert(card.querySelector('.lr-induction-proof'));assert.equal(card.querySelectorAll('.lr-process-frame').length,2);const wd=card.querySelector('.lr-atomic-wd');assert(wd&&!wd.open);assert.equal(wd.parentNode.children.at(-1),wd);
  await card.querySelector('.lr-proof-pin').click();assert.equal(view.reader.getSelection().focusLine,statement.line);assert(view.root.querySelector('.lr-detail-body .lr-induction-proof'));await view.close();
  if(editable){const input=view.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(view.root.querySelectorAll('.lr-logical-action,.lr-proof-popover,.lr-inference-toggle').length,0,'source edits invalidate every old stage');}
  view.done();
 }
 for(const locale of ['zh','en']){
  const bundle=fixture('strong'),data=records(bundle),statement=firstStatement(bundle,'ByStrongInducStmt'),record=data.result(statement.evidence),step=data.resolve(data.resolve(record.fields.body).fields.step),view=mount(bundle,locale),card=await view.hover(statement.line),part=card.querySelector('.lr-induction-proof');assert(part);assert(part.textContent.includes(locale==='zh'?'全部实例':'every instance'));
  const frame=part.querySelector('[data-process="induction-step"]');assert(frame);const forallId=step.fields.assumptions.map(value=>data.resolve(data.resolve(value).fields.store_and_infer)).map(store=>data.result(store.fields.store)).find(store=>store.type==='StoreForallFactResult').fields.fact_id.fact_id;
  assert(frame.querySelectorAll('.lr-fact-link').some(link=>link.dataset.fact===forallId),'strong induction links its actual universal hypothesis');assert(frame.textContent.includes('≤')&&frame.textContent.includes('≥'),'both lower and upper bounds are retained');view.done();
  const repeated=fixture('strong'),rv=mount(repeated,locale),instances=repeated.statements.filter(s=>s.source_statement_id===repeated.statements.find(s=>s.statement_kind==='Fact'&&s.parent_statement_id)?.source_statement_id);
  assert.equal(instances.length,2);await rv.row(instances[0].line).querySelector('.lr-line-number').click();assert.deepEqual(rv.root.querySelectorAll('.lr-contexts .lr-chip').map(chip=>chip.textContent),locale==='zh'?['基例','归纳步']:['Base case','Induction step']);
  for(const [index,instance] of instances.entries()){await rv.root.querySelectorAll('.lr-contexts .lr-chip')[index].click();await rv.close();const c=await rv.hover(instance.line);assert.equal(c.querySelector('.lr-logical-proof').dataset.statement,instance.id);assert(c.querySelector('[data-scope="'+instance.scope_id+'"]'));await rv.close();await rv.row(instance.line).querySelector('.lr-line-number').click();}rv.done();
  for(const name of ['enumeration','for']){
   const b=fixture(name),d=records(b),leaf=name==='for'?'ByForStmt':'ByEnumerateFiniteSetStmt',v=mount(b,locale);
   for(const s of b.statements.filter(s=>s.status==='accepted'&&s.statement_kind?.endsWith(leaf))){
    const r=d.result(s.evidence),c=await v.hover(s.line),part=c.querySelector('.lr-enumeration-proof');assert(part);const assignments=part.querySelectorAll('.lr-assignment-proof');assert.equal(assignments.length,r.fields.assignments.length);
    if(!assignments.length)assert(part.textContent.includes(locale==='zh'?'空真':'vacuously true'));
    for(const [index,detail] of assignments.entries()){
     assert(!detail.open);await detail.querySelector('summary').click();const stage=d.resolve(r.fields.assignments[index]),outcome=d.resolve(stage.fields.outcome),scope=d.resolve(stage.fields.local_env).scope_id,frame=detail.querySelector('.lr-process-frame');assert(frame);assert.equal(frame.dataset.scope,scope);
     if(outcome.variant==='Skipped'){assert(frame.textContent.includes(locale==='zh'?'前提被证明不成立':'premise was proved false'));assert.equal(frame.querySelectorAll('.lr-proof-step').length,1);}
     else assert.equal(frame.querySelectorAll('.lr-proof-step').length,outcome.fields.then_proofs.length);
     await expandRequirements(frame);checks++;
    }
    await v.close();
   }v.done();
  }
  for(const name of ['witness','witness-exist','witness-unique','witness-nonempty']){
   const b=fixture(name),d=records(b),v=mount(b,locale);
   for(const s of b.statements.filter(s=>s.status==='accepted'&&s.statement_kind?.startsWith('Witness.'))){
    assert(note(v,s.line,'witness'));const c=await v.hover(s.line),part=c.querySelector('.lr-witness-proof');assert(part);const r=d.result(s.evidence),obligations=d.resolve(r.fields.obligations);
    if(r.type!=='ExecWitnessNonemptySetStmtSuccessResult'){
     const frame=part.querySelector('.lr-process-frame');assert(frame);assert.equal(frame.dataset.scope,d.resolve(r.fields.local_env).scope_id);
     for(const value of r.fields.witness_equalities){const store=d.result(d.resolve(value).fields.store),id=store.fields.fact_id.fact_id;assert(frame.querySelectorAll('.lr-fact-link').some(link=>link.dataset.fact===id),'the actual witness binding is linked at the invocation, not the predicate definition');}
     if(obligations.fields.uniqueness_check)assert(part.textContent.includes(locale==='zh'?'唯一性':'Uniqueness'));
    }
    const tail=c.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);await tail.querySelector('summary').click();assert(!tail.textContent.includes('well-definedness proof was not fully exported'),name+':'+s.id+' '+tail.textContent);await expandRequirements(part);
    if(r.fields.witness_equalities?.length){const store=d.result(d.resolve(r.fields.witness_equalities[0]).fields.store),id=store.fields.fact_id.fact_id,link=part.querySelectorAll('.lr-fact-link').find(link=>link.dataset.fact===id);await link.click();assert.equal(v.reader.getSelection().fact,id);assert.equal(v.reader.getSelection().focusLine,s.line,'a witness binding navigates to its invocation');assert(v.root.querySelector('.lr-detail-body .lr-process-frame'));await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().focusLine,s.line);}
    await v.close();checks++;
   }v.done();
  }
 }
 for(const kind of ['missing-bindings','missing-body','missing-unique','missing-ambient']){
  const b=fixture('witness-unique'),d=records(b),s=firstStatement(b,'WitnessExistFact'),r=d.result(s.evidence),obligations=d.resolve(r.fields.obligations);
  if(kind==='missing-bindings')delete r.fields.witness_equalities;
  if(kind==='missing-body')delete obligations.fields.body_checks;
  if(kind==='missing-unique')delete obligations.fields.uniqueness_check;
  if(kind==='missing-ambient')delete r.fields.ambient;
  const v=mount(b,'en'),card=await v.hover(s.line);if(kind==='missing-ambient'){const wd=card.querySelector('.lr-atomic-wd');await wd.querySelector('summary').click();assert(wd.textContent.includes('not fully exported'));assert(!wd.textContent.includes('no additional domain conditions'));}else assert(/incomplete|not fully exported/.test(card.textContent),kind+' '+card.textContent);v.done();
 }
 for(const kind of ['assignments','scope','premises']){
  const b=fixture('enumeration'),d=records(b),s=firstStatement(b,'ByEnumerateFiniteSetStmt'),r=d.result(s.evidence),assignment=d.resolve(r.fields.assignments[0]);
  if(kind==='assignments')delete r.fields.assignments;
  if(kind==='scope')assignment.fields.local_env={kind:'scope',scope_id:'file:source0'};
  if(kind==='premises')delete d.resolve(assignment.fields.outcome).fields.premise_assumptions;
  const v=mount(b,'en'),card=await v.hover(s.line);if(kind==='assignments')assert(card.textContent.includes('not fully exported'));else{const detail=card.querySelector('.lr-assignment-proof');await detail.querySelector('summary').click();assert(/incomplete|not fully exported|missing/.test(detail.textContent));}v.done();
 }
 for(const kind of ['legacy','wrong-range','wrong-line','duplicate','wrong-command','wrong-scope','missing-proof']){
  const b=fixture('induction'),d=records(b),s=b.statements.find(s=>array(s.block_anchors).length),r=d.result(s.evidence),body=d.resolve(r.fields.body),base=d.resolve(body.fields.base),line=s.block_anchors.find(a=>a.role==='induction_base').line;
  if(kind==='legacy')for(const statement of b.statements)delete statement.block_anchors;
  if(kind==='wrong-range')s.block_anchors[0].start_byte=0;
  if(kind==='wrong-line')s.block_anchors[0].line++;
  if(kind==='duplicate')s.block_anchors.push({...s.block_anchors[0]});
  if(kind==='wrong-command')s.block_anchors[0]={...s.block_anchors.find(a=>a.role==='induction_step'),role:'induction_base'};
  if(kind==='wrong-scope')base.fields.local_env={kind:'scope',scope_id:'file:source0'};
  if(kind==='missing-proof')delete base.fields.goals_verified;
  const v=mount(b,'en');if(kind!=='missing-proof')assert(!note(v,line,'induction-base'),'untrusted title metadata cannot create an anchor');const c=await v.hover(s.line);assert(c.querySelector('.lr-induction-proof'));if(kind==='missing-proof')assert(c.textContent.includes('not fully exported'));if(kind==='wrong-scope')assert(c.textContent.includes('incomplete'));v.done();
 }
 for(const locale of ['zh','en'])for(const name of ['induction-actions','enumeration']){
  const b=fixture(name),v=mount(b,locale),children=b.statements.filter(s=>s.parent_statement_id&&s.statement_kind?.endsWith('ByDefStmt')&&s.inferred_fact_ids?.some(id=>s.produced_fact_ids.includes(id)));assert(children.length);
  for(const s of children){
   const instances=b.statements.filter(instance=>(instance.source_statement_id||instance.id)===(s.source_statement_id||s.id));
   if(instances.length>1){await v.close();await v.row(s.line).querySelector('.lr-line-number').click();const choices=v.root.querySelectorAll('.lr-contexts .lr-chip');assert.equal(choices.length,instances.length);assert(choices.every(chip=>chip.textContent.includes('=')),'enumeration choices show actual assignments');await choices[instances.indexOf(s)].click();await v.close();}
   const toggle=v.row(s.line).querySelector('.lr-inference-toggle');assert(toggle,'actual body-statement consequences remain on that statement, even inside a tracked process scope');const actual=JSON.parse(toggle.dataset.facts),expected=s.inferred_fact_ids.filter(id=>s.produced_fact_ids.includes(id));assert(expected.every(id=>actual.includes(id)));assert(children.filter(other=>other.id!==s.id&&other.line===s.line).every(other=>other.inferred_fact_ids.every(id=>!actual.includes(id))),'separate executions do not mix body inference results');
  }v.done();
 }
 for(const name of ['induction-false-base','induction-false-step','induction-start','strong-false-step','enumeration-false','enumeration-domain','for-false','witness-body','witness-type','witness-member','witness-unsupported-unique']){
  const b=fixture(name),v=mount(b,'en');assert.equal(b.run_result,'failure');for(const s of b.statements.filter(s=>s.status==='rejected'))assert(!note(v,s.line,'conclusion')&&!note(v,s.line,'witness'),'a rejected process cannot acquire a successful exported result');v.done();
 }
 if(process.argv[3]){
  const exported=path.resolve(process.argv[3]),manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'),'utf8')),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),dom=createDOM(),root=dom.root(),timers=new Map(),reads=[];let serial=0;
  const fetch=async url=>{const target=new URL(url);assert.equal(target.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(target.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
  vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
  const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale:'zh'}),s=whole.statements.find(s=>array(s.block_anchors).length);assert(s);
  for(const anchor of s.block_anchors){const row=root.querySelector('[data-line="'+anchor.line+'"]');assert(row.querySelector('[data-logical-kind="'+anchor.role.replace('_','-')+'"]'));await row.querySelector('.lr-source-code').trigger('pointermove');for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);await fn();}assert(root.querySelector('.lr-proof-popover .lr-process-frame'));await root.trigger('keydown',{key:'Escape'});}
  assert.equal(reads.length,1,'the actual first proof chunk is loaded once');reader.destroy();
 }
 console.log(JSON.stringify({passed:true,checks,bilingualAndReadOnly:true,exactStructuredTitleAnchors:true,baseAndStepScopesSeparate:true,strongUniversalHypothesis:true,enumerationProvedSkippedAndEmpty:true,witnessBindingsAndUniqueness:true,wdLastAndClosed:true,missingAndRejectedNotGuessed:true,sourceAndNativeRecordsUnchanged:true,actualNativeStaticChunks:!!process.argv[3]}));
}
function array(value){return Array.isArray(value)?value:[];}
run().catch(error=>{console.error(error);process.exitCode=1;});
