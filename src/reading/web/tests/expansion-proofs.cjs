'use strict';
// Native extensionality/release evidence exercised through public source events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node expansion-proofs.cjs <expansion-fixtures> [namespaced-export]');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'expansion-'+name+'.json'),'utf8'));
const leaves=new Set(['ByExtensionStmt','ByFnExtensionStmt','ReleaseObjDefStmt','ReleaseStructDefStmt','ReleaseCartDefStmt','ReleaseTupleDefStmt','ExpandRangeStmt']);
const actions=b=>b.statements.filter(s=>s.status==='accepted'&&leaves.has(s.statement_kind?.split('.').at(-1)));
function records(b){
 const nodes=new Map(b.evidence_nodes.map(row=>[row.id,row.node]));
 function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}
 function result(v){let n=resolve(v);while(n.fields?.['0'])n=resolve(n.fields['0']);return n;}
 function stores(s){const r=result(s.evidence),f=r.fields;if(r.type==='ExecReleaseObjDefStmtSuccess')return f.store_and_infer;if(r.type==='ExecReleaseStructDefStmtSuccess')return resolve(f.release).fields.store_and_infer;if(r.type==='ExecReleaseTupleDefStmtSuccess')return f.stored;return [f.store_and_infer||f.stored];}
 function outputs(s){return stores(s).map(v=>{const f=result(resolve(v).fields.store).fields;return (f.fact_id||f.whole_fact_id).fact_id;});}
 return {nodes,resolve,result,stores,outputs};
}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const view={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,line);return row;},async flush(){for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}},async move(target){if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');await view.flush();},async hover(line,focus=false){const row=view.row(line);if(focus){await row.querySelector('.lr-line-number').trigger('focus');await view.flush();}else await view.move(row.querySelector('.lr-source-code'));return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'display preserves source, proof, scope, producer and fact identity records');reader.destroy();}};
 assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length);return view;
}
const propertyIds=part=>part.querySelectorAll('.lr-expansion-properties .lr-fact-link').map(link=>link.dataset.fact);
async function expand(node){assert(node);await node.querySelector('summary').click();assert(!node.textContent.includes('cannot be matched exactly'),node.textContent);}
function wdLast(card){const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);return tail;}
async function run(){
 let checked=0;
 for(const locale of ['zh','en'])for(const editable of [true,false]){
  const b=fixture('set'),d=records(b),s=actions(b)[1],v=mount(b,locale,editable),card=await v.hover(s.line,true),part=card.querySelector('.lr-expansion-proof');assert(part);assert.equal(part.dataset.route,'set');assert(part.textContent.includes('{1, 2} ⊆ {2, 1}'));assert(part.textContent.includes('{2, 1} ⊆ {1, 2}'));assert.deepEqual(propertyIds(part),d.outputs(s));assert(!part.querySelector('.lr-expansion-properties').open);wdLast(card);const directions=part.querySelectorAll('.lr-proof-step');assert.equal(directions.length,2);for(const step of directions)await expand(step);
  await card.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert(v.root.querySelector('.lr-detail-body .lr-expansion-proof'));await v.close();const again=await v.hover(s.line);await again.querySelector('.lr-expansion-properties .lr-fact-link').click();assert.equal(v.reader.getSelection().fact,d.outputs(s)[0]);assert.equal(v.reader.getSelection().focusLine,s.line);await v.root.querySelector('.lr-back').click();assert(v.root.querySelector('.lr-detail-body .lr-expansion-proof'));await v.close();
  if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-logical-action,.lr-inference-toggle,.lr-proof-popover').length,0);}
  v.done();checked++;
 }
 for(const locale of ['zh','en'])for(const name of ['set','function','function-curried','function-callback','function-matrix','object','object-exist','object-unique','object-replacement','struct','cart','tuple','expand','expand-single']){
  const b=fixture(name),d=records(b),v=mount(b,locale);
  for(const s of actions(b)){
   const card=await v.hover(s.line),part=card?.querySelector('.lr-expansion-proof');assert(part,name+':'+s.id);assert.deepEqual(propertyIds(part),d.outputs(s),name+': only the actual publication stores');assert(!part.querySelector('.lr-empty-note'),name+': '+part.textContent);const wd=wdLast(card);await expand(wd);assert(!wd.textContent.includes('well-definedness proof was not fully exported'),name+': '+wd.textContent);
   const published=d.outputs(s),expected=[...new Set(b.inferences.filter(i=>i.producer_statement_id===s.id&&published.includes(i.source_fact_id)).flatMap(i=>i.fact_ids))].sort(),toggle=v.row(s.line).querySelector('.lr-inference-toggle'),actual=toggle?JSON.parse(toggle.dataset.facts).sort():[];assert.deepEqual(actual,expected,name+': publication-root inferences exclude WD/local proof results');
   if(part.dataset.route==='function'){assert.equal(part.querySelectorAll('.lr-complete-domain').length,2);assert(part.querySelector('.lr-domain-comparison'));const pointwise=part.querySelectorAll('.lr-proof-step').at(-1);assert(pointwise,name+':'+s.id+': '+part.textContent);await expand(pointwise);assert(pointwise.querySelector('.lr-universal-proof')||pointwise.querySelector('.lr-fact-link'),name+':'+s.id+': the native universal proof or its actual known-universal citation is available: '+pointwise.textContent);}
   if(part.dataset.route==='cart'){assert.equal(propertyIds(part).length,1);assert(!toggle,'temporary builder assumptions are not published inferences');}
   if(part.dataset.route==='tuple'){const r=d.result(s.evidence),shape=d.resolve(r.fields.shape),source=d.resolve(shape.fields.source);assert(part.querySelector('.lr-tuple-shape'));assert(part.querySelector('.lr-tuple-index-domain'));assert(part.textContent.includes('fn_set_member(f, F)'));if(source.variant==='TupleEquality'&&d.resolve(d.resolve(source.fields['0']).fields.value).fields.args.length===0)assert(part.textContent.includes(locale==='zh'?'空元组':'empty tuple'));for(const step of part.querySelectorAll('.lr-proof-step'))await expand(step);}
   if(part.dataset.route==='range'){assert(part.querySelector('.lr-range-values'));assert(part.textContent.includes(locale==='zh'?'析取':'disjunction'));await expand(part.querySelector('.lr-proof-step'));}
   checked++;
  }
  v.done();
 }
 for(const locale of ['zh','en']){
  const b=fixture('object'),d=records(b),s=actions(b)[0],v=mount(b,locale),card=await v.hover(s.line);const original=b.facts.find(f=>f.id===d.outputs(s)[0]);assert.equal(original.line,s.line-1,'native retained formula still names its original definition line');await card.querySelector('.lr-expansion-properties .lr-fact-link').click();assert.equal(v.reader.getSelection().focusLine,s.line,'publication navigation belongs to the actual release command');await v.root.querySelector('.lr-back').click();const link=v.root.querySelector('.lr-detail-body .lr-definition-link');await link.click();assert.equal(v.reader.getSelection().statement,b.statements.find(s=>s.statement_kind.endsWith('LetObjStmt')).id);v.done();
 }
 const verification=JSON.parse(fs.readFileSync(path.join(directory,'verification.json'),'utf8'));
 for(const[name,receipt]of Object.entries(verification).filter(([name])=>name.startsWith('expansion-')&&verification[name].run_result==='failure')){
  const b=fixture(name.slice('expansion-'.length)),v=mount(b,'en');assert.equal(b.run_result,'failure');if(receipt.failure_phase==='parse'){assert(b.diagnostics.some(d=>d.phase==='parse'));assert(!actions(b).length);}else{const failed=b.statements.find(s=>s.status==='rejected');assert(failed,name);const card=await v.hover(failed.line);assert(card,name);assert(!card.querySelector('.lr-expansion-proof'),'a rejected command receives no successful explanation');}v.done();checked++;
 }
 for(const control of ['left','reverse-endpoints','domain','domain-source','pointwise','pointwise-argument','lookup','released-id','struct-layer','struct-membership','cart-proof','tuple-domain','tuple-count','tuple-return','tuple-coordinate','tuple-rule','range-values','range-membership','source-kind','source-line','stores']){
  const name=control.startsWith('domain')||control.startsWith('pointwise')?'function':control.startsWith('tuple')?'tuple':control.startsWith('range')?'expand':control.startsWith('struct')?'struct':control==='cart-proof'?'cart':['lookup','released-id'].includes(control)?'object':'set',b=fixture(name),d=records(b),s=actions(b)[name==='set'?1:0],r=d.result(s.evidence),f=r.fields;
  if(control==='left')delete f.left_to_right;
  if(control==='reverse-endpoints'){const fact=d.result(d.result(f.right_to_left).fields.fact);fact.fields.left=fact.fields.right;}
  if(control==='domain')delete f.domain_match;
  if(control==='domain-source')d.resolve(d.resolve(f.right_domain).fields.source).variant='FutureDomain';
  if(control==='pointwise')delete f.pointwise_proof;
  if(control==='pointwise-argument'){const forall=d.result(d.result(f.pointwise_proof).fields.fact),equal=d.result(forall.fields.then_facts[0]),call=d.result(equal.fields.left);call.fields.body=[[]];}
  if(control==='lookup')delete f.looked_up;
  if(control==='released-id')d.result(d.resolve(f.released).fields.equal).fields.fact_id={kind:'fact_identity',fact_id:'unknown'};
  if(control==='struct-layer')d.resolve(f.release).fields.obj={kind:'unavailable'};
  if(control==='struct-membership')delete f.membership;
  if(control==='cart-proof')delete f.verification;
  if(control==='tuple-domain')delete f.domain;
  if(control==='tuple-count')f.coordinate_proofs=[];
  if(control==='tuple-return'){const fact=d.result(d.result(f.return_proofs[0]).fields.fact);fact.fields.set={kind:'unavailable'};}
  if(control==='tuple-coordinate')f.coordinate_proofs[0]=f.coordinate_proofs[1];
  if(control==='tuple-rule')d.resolve(d.resolve(f.membership_rule).fields.theorem).variant='FutureTheorem';
  if(control==='range-values')f.values=f.values.slice(1);
  if(control==='range-membership')delete f.membership;
  if(control==='source-kind')s.statement_kind='By.ByDefStmt';
  if(control==='source-line'){const store=d.result(d.resolve(f.stored).fields.store),goal=d.result(store.fields.fact);goal.fields.line_file.line++;}
  if(control==='stores')delete f.stored;
  const v=mount(b,'en'),card=await v.hover(s.line),part=card?.querySelector('.lr-expansion-proof');if(['source-kind','source-line'].includes(control))assert(!part,'conflicting native source ownership cannot borrow another command');else{assert(part,control);assert(part.querySelector('.lr-empty-note'),control+': '+part.textContent);}v.done();checked++;
 }
 if(process.argv[3]){
  const exported=path.resolve(process.argv[3]),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),data=records(whole);assert.equal(whole.run_result,'success');assert.equal(whole.sources.length,7);
  for(const locale of ['zh','en']){
   const manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'),'utf8')),dom=createDOM(),root=dom.root(),timers=new Map(),reads=[];let serial=0;
   const fetch=async url=>{const target=new URL(url);assert.equal(target.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(target.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
   vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale});
   for(const source of whole.sources){
    const s=actions(whole).find(s=>s.source_id===source.id);assert(s,source.path);await reader.selectStatement(s.id);assert(root.querySelector('.lr-detail-body .lr-expansion-proof'),source.path+': source selection retains the native expansion');await root.trigger('keydown',{key:'Escape'});const row=root.querySelector('[data-line="'+s.line+'"]');await row.querySelector('.lr-source-code').trigger('pointermove');for(let round=0;round<3;round++)for(const [id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card?.querySelector('.lr-expansion-proof'),source.path+': source hover');assert.deepEqual(propertyIds(card),data.outputs(s));assert(!/f\d+::/.test(card.textContent),'file namespaces use resolved mathematical names');wdLast(card);await root.trigger('keydown',{key:'Escape'});checked++;
   }
   assert(whole.sources.every(source=>reads.some(file=>file.endsWith(manifest.sources.find(entry=>entry.id===source.id).chunk_url))),'all seven proof chunks load through the public API');reader.destroy();
  }
 }
 console.log(JSON.stringify({passed:true,checked,bilingualEditableAndReadOnly:true,sevenNativeForms:true,bothSubsetDirections:true,completeDomainsAndPointwiseProof:true,definitionAndStructSources:true,tupleShapeDomainAndCoordinates:true,rangeAlternatives:true,actualSourceAndInferenceOwnership:true,wdLastAndClosed:true,missingAndRejectedNotGuessed:true,sourceAndNativeRecordsUnchanged:true,actualNamespacedStaticChunks:!!process.argv[3]}));
}
run().catch(e=>{console.error(e);process.exitCode=1;});
