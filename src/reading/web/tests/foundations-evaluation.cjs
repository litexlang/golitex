'use strict';
// Native foundation/eval results through the unmodified public reading API.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node foundations-evaluation.cjs <fixtures> [four-source-export]');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const leaves=new Set(['ReleaseZornLemmaStmt','ReleaseAxiomOfChoiceStmt','ReleaseRegularityAxiomStmt','EvalStmt']);
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'foundation-eval-'+name+'.json'),'utf8'));
const actions=b=>b.statements.filter(s=>s.status==='accepted'&&leaves.has(s.statement_kind?.split('.').at(-1)));
function records(b){const nodes=new Map(b.evidence_nodes.map(v=>[v.id,v.node]));function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}function result(v){let n=resolve(v);while(n.fields?.['0'])n=resolve(n.fields['0']);return n;}function output(s){const r=result(s.evidence),store=result(resolve(r.fields.store_and_infer_result||r.fields.stored).fields.store);return (store.fields.fact_id||store.fields.whole_fact_id).fact_id;}return {nodes,resolve,result,output};}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const v={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,line);return row;},async flush(){for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}},async hover(line,focus=false){const row=v.row(line);if(focus)await row.querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>row.querySelector('.lr-source-code');await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await row.querySelector('.lr-source-code').trigger('pointermove');await v.flush();return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'viewing preserves source, proof, fact identities and scopes');reader.destroy();}};
 assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length,'inline logical results do not add source rows');return v;
}
async function open(details){assert(details);await details.querySelector('summary').click();}
function wdLast(card){const wd=card.querySelector('.lr-atomic-wd');assert(wd&&!wd.open);assert.equal(wd.parentNode.children.at(-1),wd);return wd;}
async function run(){
 let checked=0,algorithms=0,functions=0,terms=0;
 const verification=JSON.parse(fs.readFileSync(path.join(directory,'verification.json'),'utf8'));
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const [key,receipt]of Object.entries(verification).filter(([n,r])=>n.startsWith('foundation-eval-')&&r.run_result==='success')){
  const name=key.slice('foundation-eval-'.length),b=fixture(name),data=records(b),v=mount(b,locale,editable);
  for(const s of actions(b)){
   const card=await v.hover(s.line,true),part=card?.querySelector('.lr-foundation-proof,.lr-evaluation-proof'),r=data.result(s.evidence),f=r.fields;assert(part,name+':'+s.line);assert(!part.querySelector('.lr-empty-note'),name+':'+s.line+': '+part.textContent);
   assert.equal(part.querySelector('.lr-command-conclusion .lr-fact-link')?.dataset.fact,data.output(s));const wd=wdLast(card);await open(wd);assert(!wd.textContent.includes('not fully exported'),name+':'+s.line+': '+wd.textContent);
   assert(v.row(s.line).querySelector('.lr-logical-action'),'actual result is anchored to the producing source row');
   if(part.dataset.route==='eval'){
    assert(part.textContent.includes(data.resolve(f.evaluated_object).text));
    if(b.sources[0].content.split('\n')[s.line-1]==='eval eval_a + 1'){assert(v.row(s.line).querySelector('.lr-logical-action').textContent.includes('→ 11'));assert(part.querySelector('.lr-evaluation-citations').textContent.includes('eval_a = 10'));assert(part.textContent.includes('10 + 1'));const link=part.querySelector('.lr-evaluation-citations .lr-fact-link');await link.click();assert.equal(v.reader.getSelection().fact,link.dataset.fact);await v.root.querySelector('.lr-back').click();assert(v.root.querySelector('.lr-detail-body .lr-evaluation-proof'));await v.close();}
    for(const trace of part.querySelectorAll('.lr-evaluation-trace')){
     assert(!trace.open,'execution details start collapsed');await open(trace);
     assert(!trace.querySelector('.lr-empty-note'),name+':'+s.line+': '+trace.textContent);
     if(trace.dataset.trace==='algo_evaluations'){assert.equal(trace.querySelectorAll('.lr-evaluation-algorithm').length,f.algo_evaluations.length);for(const proof of trace.querySelectorAll('.lr-proof-step'))await open(proof);assert(!trace.textContent.includes('cannot be matched exactly'),trace.textContent);algorithms+=f.algo_evaluations.length;}
     if(trace.dataset.trace==='function_evaluations'){assert.equal(trace.querySelectorAll('.lr-evaluation-function').length,f.function_evaluations.length);functions+=f.function_evaluations.length;}
     if(trace.dataset.trace==='aggregate_evaluations')for(const term of trace.querySelectorAll('.lr-evaluation-term')){await open(term);assert(!term.querySelector('.lr-empty-note'),name+':'+s.line+': '+term.textContent);terms++;}
    }
    if(name==='empty-sum'||name==='empty-product'){const trace=part.querySelector('[data-trace="aggregate_evaluations"]');assert(trace.textContent.includes(locale==='zh'?(name==='empty-sum'?'空和为 0':'空乘积为 1'):(name==='empty-sum'?'empty sum is 0':'empty product is 1')));}
   }else{
    assert(part.querySelector('.lr-foundation-origin').textContent.includes(locale==='zh'?'基础原理':'foundation principle'));
    const inputs=part.querySelector('.lr-foundation-inputs'),labels=inputs.querySelectorAll('dt').map(node=>node.textContent);assert.deepEqual(labels,part.dataset.route==='zorn'?(locale==='zh'?['底集','偏序关系','上界谓词','极大元谓词']:['Carrier','Partial order','Upper-bound predicate','Maximality predicate']):[part.dataset.route==='choice'?(locale==='zh'?'集合族':'Family of sets'):(locale==='zh'?'集合':'Set')]);assert(inputs.querySelector('[data-role="subject"] .lr-formula'),'the actual selected set/family is retained');
    const proofs=part.querySelectorAll('.lr-proof-step');assert.equal(proofs.length,part.dataset.route==='regularity'?1:f.obligations.length);for(const proof of proofs)await open(proof);assert(!part.textContent.includes('cannot be matched exactly'),part.textContent);
    if(part.dataset.route==='zorn'){assert.equal(part.querySelectorAll('.lr-definition-link').length,3);for(const key of ['prop_name','upper_bound_prop_name','maximal_prop_name']){const ref=data.resolve(data.resolve(f.statement).fields[key]),expected=b.statements.find(row=>row.declaration_symbol_ids?.includes(ref.symbol_id));assert(expected);const current=await v.hover(s.line),link=current.querySelector('[data-role="'+key+'"] .lr-definition-link');assert(link,key);await link.click();assert.equal(v.reader.getSelection().statement,expected.id,key+': exact declaration identity');await v.root.querySelector('.lr-back').click();assert(v.root.querySelector('.lr-detail-body .lr-foundation-inputs'));await v.close();}}
   }
   await v.close();const again=await v.hover(s.line);await again.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert(v.root.querySelector('.lr-detail-body .lr-foundation-proof,.lr-detail-body .lr-evaluation-proof'));await v.close();checked++;
  }
  if(editable){const editor=v.root.querySelector('.lr-ide-input');editor.value+='\n';await editor.trigger('input');assert.equal(v.root.querySelectorAll('.lr-logical-action,.lr-inline-inferences').length,0);assert(!v.root.querySelector('.lr-proof-popover'));}v.done();
 }
 for(const [key,receipt]of Object.entries(verification).filter(([n,r])=>n.startsWith('foundation-eval-')&&r.run_result==='failure')){const b=fixture(key.slice('foundation-eval-'.length)),v=mount(b,'en');assert.equal(b.run_result,'failure');for(const s of b.statements.filter(s=>s.status==='rejected')){const card=await v.hover(s.line);assert(!card?.querySelector('.lr-foundation-proof,.lr-evaluation-proof'),'failed execution has no successful-result bubble');}v.done();checked++;}
 for(const control of ['source-kind','source-line','source-object','result-object','output','citations','traces','wd','obligations','local-scope','steps','local-store-error']){
  const name=['obligations','local-scope','steps','local-store-error'].includes(control)?'choice':'eval',b=fixture(name),data=records(b),s=actions(b).find(s=>name==='choice'||b.sources[0].content.split('\n')[s.line-1]==='eval eval_a + 1'),r=data.result(s.evidence),f=r.fields;
  if(control==='source-kind')s.statement_kind='Fact';if(control==='source-line')s.line++;
  if(control==='source-object')f.source_object=f.evaluated_object;
  if(control==='result-object')f.evaluated_object=f.source_object;
  if(control==='output')delete f.store_and_infer_result;
  if(control==='citations')f.cited_equal_fact_ids=[{kind:'fact_reference',fact_id:'not-exported'}];
  if(control==='traces')delete f.algo_evaluations;
  if(control==='wd')delete f.source_well_defined;
  if(control==='obligations')delete f.obligations;
  if(control==='local-scope')f.local_env={kind:'scope',scope_id:'file:source0'};
  if(control==='steps')f.proof_steps=[{kind:'statement_reference',statement_id:s.id}];
  if(control==='local-store-error')data.resolve(f.obligations[0]).fields.stored={type:'Result',variant:'Err',fields:{error:'retained native storage failure'}};
  const v=mount(b,'en'),card=await v.hover(s.line),part=card?.querySelector('.lr-foundation-proof,.lr-evaluation-proof');
  if(['source-kind','source-line'].includes(control)){assert(!part||part.querySelector('.lr-empty-note'),'inconsistent source identity cannot borrow a successful source action');}
  else if(control==='wd'){await open(wdLast(card));assert(card.textContent.includes('not fully exported'));}
  else if(control==='local-store-error'){assert(part.querySelector('.lr-foundation-local-note'));assert.equal(part.querySelectorAll('.lr-command-conclusion .lr-fact-link').length,1,'failed local store does not become an additional publication');}
  else {assert(part,control);assert(part.querySelector('.lr-empty-note'),control+': '+part.textContent);}v.done();checked++;
 }
 for(const control of ['algorithm-arguments','algorithm-unchecked','algorithm-equation','function-expansion','aggregate-algorithm-index']){
  const name=control==='aggregate-algorithm-index'?'stored':control==='function-expansion'?'coordinates':'eval',b=fixture(name),data=records(b),s=actions(b).find(s=>{const f=data.result(s.evidence).fields;return control==='aggregate-algorithm-index'?f.aggregate_evaluations.length&&f.algo_evaluations.length:control==='function-expansion'?f.function_evaluations.length:f.algo_evaluations.length;}),f=data.result(s.evidence).fields;
  if(control.startsWith('algorithm')){const call=data.resolve(f.algo_evaluations[0]);if(control==='algorithm-arguments')call.fields.normalized_arguments=[];if(control==='algorithm-unchecked')call.fields.definition_evidence={type:'AlgoDefinitionEvidence',variant:'Display',fields:{}};if(control==='algorithm-equation')call.fields.return_expression={type:'Obj',variant:'Literal',fields:{},text:'999'};}
  if(control==='function-expansion')data.resolve(f.function_evaluations[0]).fields.expansion={type:'FunctionApplicationExpansionProof',variant:'Future',fields:{}};
  if(control==='aggregate-algorithm-index'){const group=data.result(f.aggregate_evaluations[0]),term=data.resolve(group.fields.terms[0]),expansion=data.resolve(term.fields.expansion);assert.equal(expansion.variant,'Algorithm');expansion.fields.evaluation_index='999999';}
  const v=mount(b,'en'),card=await v.hover(s.line),key=control==='aggregate-algorithm-index'?'aggregate_evaluations':control==='function-expansion'?'function_evaluations':'algo_evaluations',trace=card.querySelector('[data-trace="'+key+'"]');await open(trace);if(control==='aggregate-algorithm-index')await open(trace.querySelector('.lr-evaluation-term'));assert(trace.querySelector('.lr-empty-note'),'a mismatched computation must not borrow another equation or algorithm execution');v.done();checked++;
 }
 for(const locale of ['zh','en'])for(const control of ['missing-predicate','unnamed-predicate','unknown-predicate','missing-family','missing-set']){
  const name=control==='missing-family'?'choice':control==='missing-set'?'regularity':'zorn',b=fixture(name),data=records(b),s=actions(b)[0],f=data.result(s.evidence).fields,decl=data.resolve(f.statement),key='upper_bound_prop_name';
  if(control==='missing-predicate')delete decl.fields[key];if(control==='unnamed-predicate')delete data.resolve(decl.fields[key]).name;if(control==='unknown-predicate')data.resolve(decl.fields[key]).symbol_id='named:missing:upper_bound';if(control==='missing-family')delete decl.fields.family;if(control==='missing-set')delete data.result(data.result(f.nonempty).fields.fact).fields.set;
  const v=mount(b,locale),card=await v.hover(s.line),row=card.querySelector('[data-role="'+(name==='zorn'?key:'subject')+'"]');assert(row);assert(row.querySelector('.lr-empty-note'));assert(!row.querySelector('.lr-definition-link'),'missing identity cannot borrow a same-spelled definition');assert(!row.textContent.includes('undefined'));v.done();checked++;
 }
 if(process.argv[3]){
  const exported=path.resolve(process.argv[3]),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),data=records(whole);assert.equal(whole.run_result,'success');assert.equal(whole.sources.length,4);
  for(const locale of ['zh','en']){
   const manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'),'utf8')),dom=createDOM(),root=dom.root(),reads=[];
   const fetch=async url=>{const target=new URL(url);assert.equal(target.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(target.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
   vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout,clearTimeout}));const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale});
   for(const source of whole.sources){const s=actions(whole).find(s=>s.source_id===source.id);assert(s);await reader.selectStatement(s.id);const part=root.querySelector('.lr-detail-body .lr-foundation-proof,.lr-detail-body .lr-evaluation-proof');assert(part);assert.equal(part.querySelector('.lr-command-conclusion .lr-fact-link')?.dataset.fact,data.output(s));assert(!/f\d+::/.test(part.textContent),part.textContent);checked++;}
   assert(whole.sources.every(source=>reads.some(file=>file.endsWith(manifest.sources.find(s=>s.id===source.id).chunk_url))));reader.destroy();
  }
 }
 console.log(JSON.stringify({passed:true,checked,algorithms,functions,terms,fourNativeForms:true,bilingualEditableAndReadOnly:true,exactRewriteCitations:true,foundationPremisesNotAProofOfAxioms:true,localStoreFailureNotPublished:true,actualEqualityAndExistenceOutputs:true,lazyComputationTraces:true,emptyFolds:true,sourceNavigationAndPin:true,wdLastAndClosed:true,failedAndMissingNotGuessed:true,inputRecordsUnchanged:true,actualNamespacedStaticChunks:!!process.argv[3]}));
}
run().catch(e=>{console.error(e);process.exitCode=1;});
