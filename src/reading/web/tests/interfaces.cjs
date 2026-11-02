'use strict';
// Actual mathematical interfaces and definition/proof ownership, via public DOM.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node interfaces.cjs <interface-fixtures> [namespaced-export] [--require-field-anchors]');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'interface-'+name+'.json'),'utf8'));
const leaves=new Set(['DefPropStmt','DefAbstractPropStmt','DefThmStmt','DefStrategyStmt','DefStructStmt','DefTemplateStmt']),actions=b=>b.statements.filter(s=>s.status==='accepted'&&leaves.has(s.statement_kind?.split('.').at(-1)));
function records(b){const nodes=new Map(b.evidence_nodes.map(v=>[v.id,v.node]));function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}function result(v){let n=resolve(v);while(n.fields?.['0'])n=resolve(n.fields['0']);return n;}function stores(s){const r=result(s.evidence),f=r.fields;return r.type==='ExecDefThmStmtSuccess'?[f.stored]:['ExecDefStructStmtSuccessResult','ExecDefTemplateStmtSuccessResult'].includes(r.type)?f.definition_facts.map(v=>resolve(v).fields.store_and_infer):[];}function outputs(s){return stores(s).map(v=>{const f=result(resolve(v).fields.store).fields;return (f.fact_id||f.whole_fact_id).fact_id;});}return {nodes,resolve,result,stores,outputs};}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const v={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,line);return row;},async flush(){for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}},async hover(line,focus=false){const row=v.row(line);if(focus)await row.querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>row.querySelector('.lr-source-code');await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await row.querySelector('.lr-source-code').trigger('pointermove');await v.flush();return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'source, evidence, scope and native identities remain unchanged');reader.destroy();}};assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length);return v;
}
function wdLast(card){const wd=card.querySelector('.lr-atomic-wd');assert(wd&&!wd.open);assert.equal(wd.parentNode.children.at(-1),wd);return wd;}
const propertyIds=card=>card.querySelectorAll('.lr-interface-properties .lr-fact-link').map(link=>link.dataset.fact);
async function expand(step){assert(step);await step.querySelector('summary').click();assert(!step.textContent.includes('cannot be matched exactly'),step.textContent);}
async function run(){
 let checked=0,fields=0,templateBodies=0;
 const verification=JSON.parse(fs.readFileSync(path.join(directory,'verification.json'),'utf8'));
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const [key,receipt]of Object.entries(verification).filter(([name,r])=>name.startsWith('interface-')&&r.run_result==='success')){
  const name=key.slice('interface-'.length),b=fixture(name),d=records(b),v=mount(b,locale,editable);
  for(const s of actions(b)){
   const card=await v.hover(s.line,true),part=card?.querySelector('.lr-interface-definition'),r=d.result(s.evidence),f=r.fields,declaration=d.resolve(f.statement);assert(part,name+':'+s.id);assert(!part.querySelector('.lr-empty-note')||part.querySelector('.lr-empty-note').textContent.includes(locale==='zh'?'公式排版':'typesetting'),name+':'+s.id+': '+part.textContent);assert.deepEqual(propertyIds(card),d.outputs(s));const route=part.dataset.route;
   if(route==='abstract'){assert(part.textContent.includes(locale==='zh'?'未指定类型':'untyped'));assert(!part.querySelector('.lr-interface-parameters'));assert(!card.querySelector('.lr-atomic-wd'),'an untyped declaration has no invented carrier checks');}
   else {const wd=wdLast(card);await expand(wd);assert(!wd.textContent.includes('not fully exported'),name+':'+s.id+': '+wd.textContent);}
   if(route==='predicate'){
    assert(!d.outputs(s).length);assert(!v.row(s.line).querySelector('.lr-inference-toggle'),'definition preflight is not a published inference');for(const value of declaration.fields.iff_facts){const line=d.result(value).fields.line_file.line;await v.close();const condition=await v.hover(line);assert(condition?.querySelector('.lr-interface-condition'));assert(!condition.querySelector('.lr-proof-application'),'a definition clause is not a proved instance');wdLast(condition);}
   }
   if(route==='theorem'||route==='strategy'){
    if(route==='strategy')assert(!d.outputs(s).length,'strategy registration does not publish an ordinary universal');await v.close();const proof=(await v.hover(s.line)).querySelector('.lr-interface-definition');for(const step of proof.querySelectorAll('.lr-proof-step'))await expand(step);
   }
   if(route==='struct'){
    const anchors=(s.block_anchors||[]).filter(a=>a.role==='structure_field');if(process.argv.includes('--require-field-anchors'))assert.equal(anchors.length,declaration.fields.fields.length,name+':'+s.id+': exact native field anchors required');await v.close();const header=await v.hover(s.line);assert.equal(header.querySelectorAll('.lr-field-link').length,anchors.length,'legacy data never guesses field lines');for(const anchor of anchors){await v.close();const field=await v.hover(anchor.line);assert(field?.querySelector('.lr-interface-condition[data-role="structure-field"]'));wdLast(field);fields++;}
   }
   if(route==='template'){
    const body=d.result(f.body),original=d.result(declaration.fields.template_def_stmt);assert.equal(original,d.resolve(body.fields.statement));const line=original.fields.line_file.line;await v.close();const bodyCard=await v.hover(line);assert(bodyCard?.querySelector('.lr-function-definition,.lr-introduction-proof,.lr-context-change-proof'),name+':'+s.id+': '+bodyCard?.textContent);assert(!bodyCard.textContent.includes('source is incomplete'),bodyCard.textContent);assert.equal(v.row(line).dataset.statement,s.id,'native body execution remains owned by the template, without a fabricated source Stmt');wdLast(bodyCard);templateBodies++;
   }
   await v.close();const again=await v.hover(s.line);await again.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert(v.root.querySelector('.lr-detail-body .lr-interface-definition'));await v.close();checked++;
  }
  if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-logical-action,.lr-inference-toggle,.lr-proof-popover').length,0);}v.done();
 }
 for(const [key,r]of Object.entries(verification).filter(([name,r])=>name.startsWith('interface-')&&r.run_result==='failure')){const b=fixture(key.slice('interface-'.length)),v=mount(b,'en');assert.equal(b.run_result,'failure');for(const s of b.statements.filter(s=>s.status==='rejected')){const card=await v.hover(s.line);assert(!card?.querySelector('.lr-interface-definition'),'a rejected definition receives no successful interface card');}v.done();checked++;}
 for(const control of ['name','source-kind','predicate-checks','predicate-order','theorem-scope','theorem-goal','strategy-proof','struct-checks','struct-source','template-body','template-source','template-stores']){
  const name=control.startsWith('predicate')?'prop':control.startsWith('theorem')?'theorem':control.startsWith('strategy')?'strategy':control.startsWith('struct')?'struct':control.startsWith('template')?'template':'prop',b=fixture(name),d=records(b),s=actions(b).filter(s=>name==='strategy'?s.statement_kind.endsWith('DefStrategyStmt'):true)[control==='predicate-order'?2:0],r=d.result(s.evidence),f=r.fields,declaration=d.resolve(f.statement);
  if(control==='name')declaration.fields.name={kind:'symbol_reference',symbol_id:'missing',name:'missing'};
  if(control==='source-kind')s.statement_kind='Definition.LetObjStmt';
  if(control==='predicate-checks')delete f.assumed_iff_facts;
  if(control==='predicate-order')f.assumed_iff_facts.reverse();
  if(control==='theorem-scope')f.local_env={kind:'scope',scope_id:'file:source0'};
  if(control==='theorem-goal')delete declaration.fields.fact;
  if(control==='strategy-proof')d.result(f.body).fields.conclusion_proofs=[];
  if(control==='struct-checks')d.resolve(f.field_scope).fields.fields=[];
  if(control==='struct-source'){const selected=actions(b).find(s=>d.result(s.evidence).fields.definition_facts?.length);if(selected){const pair=d.resolve(d.result(selected.evidence).fields.definition_facts[0]);pair.fields.source_fact_id={kind:'fact_reference',fact_id:'missing'};}else throw new Error('need actual published struct law');}
  if(control==='template-body')delete f.body;
  if(control==='template-source')d.resolve(f.definition_facts[0]).fields.source_fact_id={kind:'fact_reference',fact_id:'missing'};
  if(control==='template-stores')delete f.definition_facts;
  const target=control==='struct-source'?actions(b).find(s=>d.result(s.evidence).fields.definition_facts?.length):s,v=mount(b,'en'),card=await v.hover(target.line),part=card?.querySelector('.lr-interface-definition');if(['name','source-kind'].includes(control)){if(part)assert(part.querySelector('.lr-empty-note'));}else{assert(part,control);assert(part.querySelector('.lr-empty-note'),control+': '+part.textContent);}v.done();checked++;
 }
 if(actions(fixture('struct')).some(s=>s.block_anchors?.some(a=>a.role==='structure_field')))for(const control of ['binding','index','range','duplicate','legacy']){
  const b=fixture('struct'),s=actions(b)[0],anchor=s.block_anchors.find(a=>a.role==='structure_field');assert(anchor);const line=anchor.line;
  if(control==='binding')anchor.symbol_id='unknown';if(control==='index')anchor.index=123;if(control==='range')anchor.source_text+='wrong';if(control==='duplicate')s.block_anchors.push({...anchor});if(control==='legacy')delete s.block_anchors;
  const v=mount(b,'en'),header=await v.hover(s.line);assert.equal(header.querySelectorAll('.lr-field-link').length,control==='legacy'?0:1);await v.close();assert(!(await v.hover(line))?.querySelector('.lr-interface-condition[data-role="structure-field"]'),'unmatched or old field metadata cannot guess a line');v.done();checked++;
 }
 const exportedArg=process.argv[3]&&!process.argv[3].startsWith('--')?process.argv[3]:null;
 if(exportedArg){
  const exported=path.resolve(exportedArg),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),data=records(whole);assert.equal(whole.run_result,'success');assert.equal(whole.sources.length,6);
  for(const locale of ['zh','en']){
   const manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'),'utf8')),dom=createDOM(),root=dom.root(),timers=new Map(),reads=[];let serial=0;
   const fetch=async url=>{const target=new URL(url);assert.equal(target.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(target.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
   vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale});
   for(const source of whole.sources){
    const s=actions(whole).find(s=>s.source_id===source.id);assert(s,source.path);await reader.selectStatement(s.id);assert(root.querySelector('.lr-detail-body .lr-interface-definition'));await root.trigger('keydown',{key:'Escape'});const row=root.querySelector('[data-line="'+s.line+'"]');await row.querySelector('.lr-source-code').trigger('pointermove');for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card?.querySelector('.lr-interface-definition'));assert.deepEqual(propertyIds(card),data.outputs(s));assert(!/f\d+::/.test(card.textContent),source.path+': '+card.textContent);await root.trigger('keydown',{key:'Escape'});checked++;
   }
   assert(whole.sources.every(source=>reads.some(file=>file.endsWith(manifest.sources.find(s=>s.id===source.id).chunk_url))));reader.destroy();
  }
 }
 console.log(JSON.stringify({passed:true,checked,fieldChecks:fields,templateBodies,sixNativeInterfaces:true,bilingualEditableAndReadOnly:true,definitionNotInstanceProof:true,untypedAbstractParameters:true,theoremAndStrategyPublicationSeparate:true,structFieldsAndTemplateBodyOwnership:true,wdLastAndClosed:true,actualFailuresRetained:true,missingAndConflictingEvidenceNotGuessed:true,nativeRecordsUnchanged:true,actualNamespacedStaticChunks:!!exportedArg}));
}
run().catch(e=>{console.error(e);process.exitCode=1;});
