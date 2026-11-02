'use strict';
// Native per-conclusion rule identities and their real source/side conditions.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node inferred-rules.cjs <fixtures> [actual-export]');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'inferred-rule-'+name+'.json'),'utf8'));
function records(bundle){const nodes=new Map(bundle.evidence_nodes.map(item=>[item.id,item.node]));const resolve=value=>{while(value?.kind==='evidence_reference')value=nodes.get(value.evidence_id);return value||{};};return {nodes,resolve};}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 return {...dom,root,reader,async hover(target){if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let i=0;i<3;i++)for(const [id,fn]of [...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},done(){assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources.find(s=>s.id===reader.getSelection().source).content.split('\n').length);assert.equal(JSON.stringify(bundle),before,'viewer preserves native source, facts, rule effects and scopes');reader.destroy();}};
}
async function run(){
 let checked=0;const families=new Set(),missingDescriptions=new Set();
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const name of ['definitions','nested-predicate','rule-families','nonzero-cancellation','function-range','union','builder','function-carrier','template','injective']){
  const b=fixture(name),v=mount(b,locale,editable),seen=new Set();
  for(const batch of b.inferences){
   const producer=b.statements.find(s=>s.id===batch.producer_statement_id);if(producer?.status!=='accepted')continue;
   for(const origin of batch.conclusion_origins||[]){
    const fact=b.facts.find(f=>f.id===origin.fact_id);if(!fact||fact.evidence||['verified','hypothesis'].includes(fact.role)||fact.producer_statement_id!==producer.id||!origin.rule_id)continue;
    const key=origin.rule_id+':'+fact.scope_id+':'+producer.id;if(name!=='definitions'&&seen.has(key))continue;seen.add(key);
    await v.reader.selectFact(fact.id);let panel=v.root.querySelector('.lr-detail-body'),part=panel.querySelector('.lr-inference-proof');assert(part,name+': '+fact.text);
    assert.equal(part.dataset.sourceFact,batch.source_fact_id);assert.equal(part.dataset.scope,fact.scope_id);
    const expected=[...new Set(batch.conclusion_origins.filter(o=>o.fact_id===fact.id&&o.rule_id).map(o=>o.rule_id))],shown=part.querySelectorAll('.lr-inference-rule').map(node=>node.dataset.rule);assert.deepEqual(shown,expected,'a result has its own rules, not the full batch list');expected.forEach(id=>families.add(id));
    assert(!part.querySelector('.lr-equivalence'),'a one-way inferred result is not displayed as the entire defining equivalence');
    if(part.textContent.includes(locale==='zh'?'数学说明尚未提供':'mathematical description of this rule is not yet available'))expected.forEach(id=>missingDescriptions.add(id));
    const link=part.querySelector('[data-fact="'+batch.source_fact_id+'"]');assert(link);if(b.facts.find(f=>f.id===batch.source_fact_id).role==='hypothesis')assert(link.querySelector('small'),'an assumed source keeps its assumption label');await link.click();assert.equal(v.reader.getSelection().fact,batch.source_fact_id);await v.root.querySelector('.lr-back').click();part=v.root.querySelector('.lr-inference-proof');assert(part);
    if(origin.definition_statement_id){const definition=part.querySelector('.lr-definition-link');assert(definition);await definition.click();assert.equal(v.reader.getSelection().statement,origin.definition_statement_id);await v.root.querySelector('.lr-back').click();}
    const requirements=v.root.querySelector('.lr-inference-proof .lr-inference-requirements');if(requirements){assert(!requirements.open);await requirements.querySelector('summary').click();assert(requirements.querySelector('.lr-proof-step,.lr-fact-link'));if(origin.rule_id.endsWith('::NonzeroFactorCancellation'))assert(requirements.textContent.includes('≠ 0'),'nonzero cancellation exposes its actual nonzero check');}
    checked++;
   }
  }
  if(name==='definitions'){
   const stmt=b.statements.find(s=>s.statement_kind.endsWith('ByDefStmt')),row=v.root.querySelector('[data-line="'+stmt.line+'"]'),toggle=row.querySelector('.lr-inference-toggle');assert(toggle);await toggle.click();const list=v.root.querySelector('.lr-inferred-facts');assert(list&&!list.open,'ordinary inferred facts remain folded');await list.querySelector('summary').click();await list.querySelector('.lr-inferred-result').click();assert(v.root.querySelector('.lr-inference-proof'));assert.equal(v.reader.getSelection().focusLine,stmt.line);
   await v.root.trigger('keydown',{key:'Escape'});const typed=v.root.querySelector('[data-line="'+stmt.line+'"]').querySelectorAll('[data-syntax]').find(token=>token.textContent==='nonnegative');assert(typed);const card=await v.hover(typed);assert(card.querySelector('.lr-proof-evidence .lr-predicate-application'),'the original instance retains its direct definition proof');assert(!card.querySelector('.lr-proof-evidence .lr-inference-proof'));
  }
  if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-inference-toggle,.lr-proof-popover').length,0);}v.done();
 }
 assert(families.size>=14,'independent native inference families are exercised');assert.equal(missingDescriptions.size,0,'the selected native rules have bilingual mathematical descriptions');
 for(const control of ['missing-origins','wrong-origin','foreign-definition','missing-rule-index','foreign-rule-descriptor','missing-native-effect','wrong-store-id','missing-store-subject','missing-source-store','wrong-source','foreign-producer','foreign-scope','conflicting-known-scope']){
  const b=fixture('definitions'),d=records(b),batch=b.inferences[0],origin=batch.conclusion_origins[0],id=origin.fact_id,rule=origin.rule_id,leaf=[...d.nodes.values()].find(node=>node.type==='StoreInferredFactResult'&&node.stored_fact_ids?.includes(id));
  if(control==='missing-origins')delete batch.conclusion_origins;if(control==='wrong-origin')origin.rule_id=batch.rule_ids.find(value=>value!==rule);if(control==='foreign-definition')origin.source_symbol_id='foreign';if(control==='missing-rule-index')batch.rule_ids=[];if(control==='foreign-rule-descriptor')b.rules.find(r=>r.id===rule).variant='Wrong';
  if(control==='missing-native-effect')delete leaf.stored_fact_ids;
  let store=d.resolve(leaf.fields.store);while(store.fields?.['0'])store=d.resolve(store.fields['0']);
  if(control==='wrong-store-id')store.fields.fact_id={kind:'fact_reference',fact_id:batch.fact_ids.find(value=>value!==id)};if(control==='missing-store-subject')delete store.fields.fact;
  if(control==='missing-source-store')for(const node of d.nodes.values())if(node.type==='StoreFactAndInferResult'&&node.fields.infer?.evidence_id===batch.evidence.evidence_id)delete node.fields.store;
  if(control==='wrong-source')batch.source_fact_id=b.facts.find(f=>f.id!==batch.source_fact_id&&f.role==='verified').id;if(control==='foreign-producer')batch.producer_statement_id='foreign';if(control==='foreign-scope')b.facts.find(f=>f.id===id).scope_id='foreign';if(control==='conflicting-known-scope')b.facts.find(f=>f.id===id).scope_id=b.scopes.find(s=>s.id!==batch.scope_id).id;
  const v=mount(b,'en');await v.reader.selectFact(id);const panel=v.root.querySelector('.lr-detail-body'),part=panel.querySelector('.lr-inference-proof');
  if(['missing-source-store','wrong-source','foreign-producer','foreign-scope','conflicting-known-scope'].includes(control)){assert(!part);assert(!panel.querySelector('.lr-definition-link'));assert(panel.textContent.includes('not fully exported'));}
  else{assert(part);if(['missing-rule-index','foreign-rule-descriptor','missing-native-effect','wrong-store-id','missing-store-subject'].includes(control)){assert(!part.querySelector('.lr-inference-rule'));assert(part.textContent.includes('not fully exported'));}else{assert.deepEqual(part.querySelectorAll('.lr-inference-rule').map(n=>n.dataset.rule),[rule]);assert(!part.querySelector('.lr-definition-link'));}}v.done();checked++;
 }
 for(const origin of ['trust','checked']){const b=fixture('definitions'),s=b.statements.find(s=>s.statement_kind.endsWith('ByDefStmt')),batch=b.inferences.find(batch=>batch.producer_statement_id===s.id);s.origin=origin;if(origin==='checked')s.trust_dependencies=[b.statements[0].id];const v=mount(b,'en');await v.reader.selectFact(batch.fact_ids[0]);assert(v.root.querySelector('.lr-inference-proof .lr-origin-note'),'UI-only source-origin controls preserve dependency qualifications');v.done();checked++;}
 if(process.argv[3]){
  const exported=path.resolve(process.argv[3]),manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'))),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'))),dom=createDOM(),root=dom.root(),reads=[];
  const fetch=async url=>{const u=new URL(url);assert.equal(u.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(u.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file))};};
  vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout,clearTimeout}));const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale:'zh'}),statement=whole.statements.find(s=>s.statement_kind.endsWith('ByDefStmt'));await reader.selectStatement(statement.id);const toggle=root.querySelector('[data-line="'+statement.line+'"] .lr-inference-toggle');await toggle.click();await root.querySelector('.lr-inferred-facts summary').click();await root.querySelector('.lr-inferred-result').click();assert(root.querySelector('.lr-inference-proof .lr-inference-rule'));assert.equal(reads.length,1);reader.destroy();
 }
 console.log(JSON.stringify({passed:true,checked,nativeRules:[...families],missingDescriptions:[...missingDescriptions],bilingualEditableAndReadOnly:true,actualPerConclusionRules:true,sourceAndDefinitionNavigation:true,nativeSideConditions:true,closedByDefault:true,missingOrForeignNotBorrowed:true,sourceAndProofRecordsUnchanged:true,actualNativeExport:!!process.argv[3],browserObserved:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
