'use strict';
// Real checked registrations, explicit assumptions and discarded local scopes.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node context-changes.cjs <state-change-fixtures> [namespaced-export]');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'context-change-'+name+'.json'),'utf8'));
const leaves=new Set(['RegisterReflexivePropStmt','RegisterSymmetricPropStmt','RegisterTransitivePropStmt','TrustStmt','TrustHaveStmt','AxiomStmt','SketchStmt']);
const actions=b=>b.statements.filter(s=>s.status==='accepted'&&leaves.has(s.statement_kind?.split('.').at(-1)));
function records(b){const nodes=new Map(b.evidence_nodes.map(v=>[v.id,v.node]));function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}function result(v){let n=resolve(v);while(n.fields?.['0'])n=resolve(n.fields['0']);return n;}function stores(s){const r=result(s.evidence),f=r.fields;if(r.type==='ExecTrustStmtSuccessResult')return f.store_and_infer_results;if(r.type==='ExecTrustHaveStmtSuccessResult')return [...resolve(f.defined_param_store_and_infer).fields.store_and_infer_results,...f.body_store_and_infer_results,...(f.auto_opened_struct_layers||[]).flatMap(v=>resolve(v).fields.store_and_infer)];if(r.type==='ExecAxiomStmtSuccess')return [f.stored];return [];}function outputs(s){return stores(s).map(v=>{const f=result(resolve(v).fields.store).fields;return (f.fact_id||f.whole_fact_id).fact_id;});}return {nodes,resolve,result,stores,outputs};}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const v={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,line);return row;},async flush(){for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}},async hover(line,focus=false){const row=v.row(line);if(focus)await row.querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>row.querySelector('.lr-source-code');await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await row.querySelector('.lr-source-code').trigger('pointermove');await v.flush();return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'source, proof, scope and producer identities remain unchanged');reader.destroy();}};assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length);return v;
}
function wdLast(card){const wd=card.querySelector('.lr-atomic-wd');assert(wd&&!wd.open);assert.equal(wd.parentNode.children.at(-1),wd);return wd;}
const ids=card=>card.querySelectorAll('.lr-context-properties .lr-fact-link').map(link=>link.dataset.fact);
async function run(){
 let checked=0;
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const name of ['reflexive','symmetric','transitive','trust','trust-have','trust-have-release','axiom','sketch']){
  const b=fixture(name),d=records(b),v=mount(b,locale,editable);
  for(const s of actions(b)){
   const card=await v.hover(s.line,true),part=card?.querySelector('.lr-context-change-proof');assert(part,name+':'+s.id);assert(!part.querySelector('.lr-empty-note'),part.textContent);assert.deepEqual(ids(card),d.outputs(s));const route=part.dataset.route;
   const at=new Map([[s.line,[]]]);for(const store of d.stores(s)){const output=d.result(d.resolve(store).fields.store).fields,id=(output.fact_id||output.whole_fact_id).fact_id,line=d.result(output.fact).fields.line_file?.line||s.line;if(!at.has(line))at.set(line,[]);at.get(line).push(...b.inferences.filter(i=>i.producer_statement_id===s.id&&i.source_fact_id===id).flatMap(i=>i.fact_ids));}for(const [line,expected]of at){const toggle=v.row(line).querySelector('.lr-inference-toggle'),actual=toggle?JSON.parse(toggle.dataset.facts):[];assert.deepEqual([...new Set(actual)].sort(),[...new Set(expected)].sort(),name+': '+line+': actual published consequences stay at their own source row');if(toggle)assert.equal(toggle.getAttribute('aria-expanded'),'false');}
   if(route==='registration'){
    assert(!d.outputs(s).length,'registration installs a property rather than publishing a universal store');assert(part.querySelector('.lr-definition-link'));const law=part.querySelector('.lr-proof-step');assert(law);await law.querySelector('summary').click();assert(law.querySelector('.lr-universal-proof')||law.querySelector('.lr-fact-link'));assert(!law.textContent.includes('cannot be matched exactly'));wdLast(card);await part.querySelector('.lr-definition-link').click();assert(v.reader.getSelection().statement!==s.id);await v.root.querySelector('.lr-back').click();await v.close();
   }else if(route==='sketch'){
    assert(!ids(card).length);assert(!card.querySelector('.lr-atomic-wd'),'a scratch block has no invented goal formation check');const local=d.resolve(d.result(s.evidence).fields.local_env).scope_id;assert(b.scopes.some(scope=>scope.id===local));const list=part.querySelector('.lr-context-local-steps');assert(list&&!list.open);await list.querySelector('summary').click();assert(list.querySelector('.lr-math-link'));await list.querySelector('.lr-math-link').click();assert.equal(b.statements.find(row=>row.id===v.reader.getSelection().statement).parent_statement_id,s.id);await v.root.querySelector('.lr-back').click();await v.close();
   }else{
    assert(part.querySelector('.lr-explicit-assumption'));assert(!part.querySelector('.lr-context-properties').open);assert(!part.querySelector('.lr-proof-step'),'assumed truth is never given a fabricated proof');const wd=wdLast(card);await wd.querySelector('summary').click();assert(!wd.textContent.includes('not fully exported'),wd.textContent);const first=part.querySelector('.lr-fact-link');await first.click();assert.equal(v.reader.getSelection().fact,d.outputs(s)[0]);assert(v.root.querySelector('.lr-detail-body .lr-explicit-assumption'));await v.root.querySelector('.lr-back').click();await v.close();
   }
   const again=await v.hover(s.line);await again.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert(v.root.querySelector('.lr-detail-body .lr-context-change-proof'));await v.close();checked++;
  }
  if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-logical-action,.lr-inference-toggle,.lr-proof-popover').length,0);}v.done();
 }
 const verification=JSON.parse(fs.readFileSync(path.join(directory,'verification.json'),'utf8'));
 for(const locale of ['zh','en']){
  const b=fixture('trust-have-release'),d=records(b),s=b.statements.find(s=>s.status==='accepted'&&s.statement_kind.endsWith('ReleaseObjDefStmt')),v=mount(b,locale),card=await v.hover(s.line);assert(card.querySelector('.lr-release-assumption'),'releasing a trusted definition retains its explicit assumption origin');assert(card.querySelector('.lr-release-assumption').textContent.includes('trust have'));assert(!card.querySelector('.lr-definition-application'),'no proof is invented for the assumed defining equation');assert.equal(d.resolve(d.result(s.evidence).fields.released).variant,'TrustHave');v.done();checked++;
  const reuse=fixture('trust-have'),source=reuse.sources[0].content.split('\n'),used=reuse.statements.find(s=>s.statement_kind==='Fact'&&source[s.line-1]==='trusted_a = 1'),rv=mount(reuse,locale),proof=await rv.hover(used.line);assert(proof.querySelector('.lr-origin-note'),'later use retains native trust dependencies');assert(proof.querySelector('.lr-fact-link'),'later use cites the actual accepted assumption');rv.done();checked++;
 }
 for(const [name,receipt]of Object.entries(verification).filter(([name,r])=>name.startsWith('context-change-')&&r.run_result==='failure')){
  const b=fixture(name.slice('context-change-'.length)),v=mount(b,'en');assert.equal(b.run_result,'failure');for(const s of b.statements.filter(s=>s.status==='rejected')){const card=await v.hover(s.line);assert(!card?.querySelector('.lr-context-change-proof'),'rejection has no successful registration or assumption action');}if(receipt.strict&&name.includes('strict-'))assert(!actions(b).some(s=>['TrustStmt','TrustHaveStmt','AxiomStmt'].some(leaf=>s.statement_kind.endsWith(leaf))));v.done();checked++;
 }
 for(const control of ['law','prop','registration-scope','source-kind','source-command','axiom-goal','trust-stores','trust-order','trust-wd','have-stores','have-body','have-layers','sketch-scope','sketch-steps']){
  const name=control.startsWith('sketch')?'sketch':control.startsWith('have')?'trust-have':control.startsWith('trust')?'trust':control==='axiom-goal'?'axiom':'symmetric',b=fixture(name),d=records(b),s=actions(b)[control==='trust-order'?1:0],r=d.result(s.evidence),f=r.fields;
  if(control==='law')delete f.forall_proof;
  if(control==='prop')f.prop={kind:'symbol_reference',symbol_id:'unknown',name:'unknown'};
  if(control==='registration-scope'||control==='sketch-scope')f.local_env={kind:'scope',scope_id:'file:source0'};
  if(control==='source-kind')s.statement_kind='Definition.DefPropStmt';
  if(control==='source-command')s.line++;
  if(control==='axiom-goal')delete d.resolve(f.statement).fields.forall_fact;
  if(control==='trust-stores')delete f.store_and_infer_results;
  if(control==='trust-order')f.store_and_infer_results.reverse();
  if(control==='trust-wd')delete f.facts_well_defined;
  if(control==='have-stores')delete f.defined_param_store_and_infer;
  if(control==='have-body')f.body_store_and_infer_results=[];
  if(control==='have-layers')f.auto_opened_struct_layers=[{type:'FutureLayer',fields:{}}];
  if(control==='sketch-steps')f.proof_steps=[{kind:'statement_reference',statement_id:s.id}];
  const v=mount(b,'en'),card=await v.hover(s.line),part=card?.querySelector('.lr-context-change-proof');if(['source-kind','source-command'].includes(control))assert(!part,'conflicting source ownership cannot borrow a successful action');else if(control==='trust-wd'){const wd=wdLast(card);await wd.querySelector('summary').click();assert(wd.textContent.includes('not fully exported'));}else{assert(part,control);assert(part.querySelector('.lr-empty-note'),control+': '+part.textContent);}v.done();checked++;
 }
 if(process.argv[3]){
  const exported=path.resolve(process.argv[3]),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),data=records(whole);assert.equal(whole.run_result,'success');assert.equal(whole.sources.length,7);
  for(const locale of ['zh','en']){
   const manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'),'utf8')),dom=createDOM(),root=dom.root(),timers=new Map(),reads=[];let serial=0;
   const fetch=async url=>{const target=new URL(url);assert.equal(target.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(target.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
   vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale});
   for(const source of whole.sources){
    const s=actions(whole).find(s=>s.source_id===source.id);assert(s,source.path);await reader.selectStatement(s.id);assert(root.querySelector('.lr-detail-body .lr-context-change-proof'));await root.trigger('keydown',{key:'Escape'});const row=root.querySelector('[data-line="'+s.line+'"]');await row.querySelector('.lr-source-code').trigger('pointermove');for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card?.querySelector('.lr-context-change-proof'));assert.deepEqual(ids(card),data.outputs(s));assert(!/f\d+::/.test(card.textContent));await root.trigger('keydown',{key:'Escape'});checked++;
   }
   assert(whole.sources.every(source=>reads.some(file=>file.endsWith(manifest.sources.find(s=>s.id===source.id).chunk_url))));reader.destroy();
  }
 }
 console.log(JSON.stringify({passed:true,checked,sevenNativeForms:true,bilingualEditableAndReadOnly:true,registrationProvesLawBeforeInstalling:true,trustIsNotProof:true,axiomOriginRetained:true,releaseRetainsTrustOrigin:true,sketchPublishesNothing:true,sourceNavigationAndPin:true,wdLastAndClosed:true,strictAndWdAndParseRejections:true,missingAndConflictingRecordsNotGuessed:true,inputRecordsUnchanged:true,actualNamespacedStaticChunks:!!process.argv[3]}));
}
run().catch(e=>{console.error(e);process.exitCode=1;});
