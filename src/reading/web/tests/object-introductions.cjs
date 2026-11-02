'use strict';
// Actual object introduction, witnessed properties and source identities.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node object-introductions.cjs <introduction-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'intro-'+name+'.json'),'utf8'));
const leaves=new Set(['LetObjStmt','HaveObjInNonemptySetStmt','HaveObjEqualStmt','HaveObjByExistFactsStmt','ObtainObjFromExistFact','ObtainObjFromAtomicFact','HaveByPreimageStmt','HaveByReplacementAxiomStmt']);
const introductions=bundle=>bundle.statements.filter(s=>s.status==='accepted'&&leaves.has(s.statement_kind?.split('.').at(-1)));
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
  async move(target){if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);await fn();}},
  async hover(line,focus=false){const row=view.row(line);if(focus){await row.querySelector('.lr-line-number').trigger('focus');for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);await fn();}}else await view.move(row.querySelector('.lr-source-code'));return root.querySelector('.lr-proof-popover');},
  async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'display never changes source, actual stores, native proof or scope records');reader.destroy();}};
 assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length,'introduction annotations add no source rows');return view;
}
const propertyIds=part=>part.querySelectorAll('.lr-introduction-properties .lr-fact-link').map(link=>link.dataset.fact);
function outputRoots(data,record){
 const f=record.fields;if(record.type==='ExecLetObjStmtSuccessResult')return f.stored_fact_ids.map(id=>id.fact_id);
 const stores=data.resolve(f.store_and_infer_result||f.defined_params).fields.store_and_infer_results.slice();if(record.type==='ExecHaveByReplacementAxiomStmtSuccessResult')stores.push(f.introduction,f.elimination);
 for(const layer of f.auto_opened_struct_layers||[])stores.push(...data.resolve(layer).fields.store_and_infer);
 return stores.map(value=>{const store=data.result(data.resolve(value).fields.store);return (store.fields.fact_id||store.fields.whole_fact_id).fact_id;});
}
async function expand(step){assert(step);await step.querySelector('summary').click();assert(!step.textContent.includes('cannot be matched exactly'),step.textContent);}
async function run(){
 let checked=0;
 for(const locale of ['zh','en'])for(const editable of [true,false]){
  const b=fixture('obtain-atomic'),d=records(b),v=mount(b,locale,editable),s=introductions(b)[0],r=d.result(s.evidence),expected=outputRoots(d,r);let card=await v.hover(s.line,true),part=card.querySelector('.lr-introduction-proof');assert(part);assert.equal(part.dataset.route,'obtain-atomic');assert.deepEqual(propertyIds(part),expected);assert(part.textContent.includes('a = 2'));assert(part.textContent.includes('x ↦ atomic_a'));assert(!part.textContent.includes('x = atomic_a'),'witness naming is not a new equality about a free x');assert(!v.row(s.line).dataset.proofFacts,'an internal existential WD hypothesis cannot own the source row');
  const wd=card.querySelector('.lr-atomic-wd');assert(wd&&!wd.open);assert.equal(wd.parentNode.children.at(-1),wd);await expand(wd);assert(!wd.textContent.includes('not fully exported'),wd.textContent);
  const proof=card.querySelector('.lr-proof-evidence'),symbol=v.row(s.line).querySelectorAll('[data-symbol]').find(token=>token.textContent==='atomic_a');assert(symbol);await v.move(symbol);assert.strictEqual(v.root.querySelector('.lr-proof-popover .lr-proof-evidence'),proof);const info=card.querySelector('.lr-proof-symbol');assert(!info.hidden);assert.deepEqual(propertyIds(info),expected,'object hover shows only properties of the actual introduced symbol');assert(info.querySelector('.lr-introduction-link'));
  const sourceStep=part.querySelector('.lr-proof-step');await expand(sourceStep);assert(sourceStep.querySelector('.lr-fact-link'),'the predicate proof cites the established instance');
  await part.querySelector('.lr-definition-link').click();assert.equal(v.reader.getSelection().statement,b.statements.find(s=>s.statement_kind.endsWith('DefPropStmt')).id);await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().statement,s.id);assert(v.root.querySelector('.lr-detail-body .lr-introduction-proof'));await v.close();
  card=await v.hover(s.line);await card.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert(v.root.querySelector('.lr-detail-body .lr-introduction-proof'));await v.close();
  if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-logical-action,.lr-inference-toggle,.lr-proof-popover').length,0,'source edits invalidate retained introductions');}
  v.done();checked++;
 }
 for(const locale of ['zh','en']){
  for(const name of ['let','have','equal','dependent','have-exist','have-comparison','obtain-exist','obtain-atomic','preimage','preimage-multiple','preimage-returned','preimage-field','local','finite','replacement','scope','contra']){
   const b=fixture(name),d=records(b),v=mount(b,locale);
   for(const s of introductions(b)){
    const r=d.result(s.evidence),card=await v.hover(s.line),part=card?.querySelector('.lr-introduction-proof');assert(part,name+':'+s.id);assert.deepEqual(propertyIds(part),outputRoots(d,r),name+': each introduced property retains its exact native identity');
    assert(!part.textContent.includes('not fully exported')&&!part.textContent.includes('incomplete'),name+':'+s.id+' '+part.textContent);
    const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);await expand(tail);assert(!tail.textContent.includes('well-definedness proof was not fully exported'),name+':'+s.id+' '+tail.textContent);
    if(['let','have','equal','finite'].includes(name))assert(!v.row(s.line).querySelector('[data-logical-kind="object-introduction"]'),'explicit declarations do not gain another visible button');
    if(name==='replacement'){assert(part.textContent.includes(locale==='zh'?'替换公理':'Axiom of Replacement'));assert(part.textContent.includes(locale==='zh'?'至多':'at most'));assert(part.textContent.includes(locale==='zh'?'存在':'There exists'),'nested forall/exist properties retain the existential quantifier');const context=part.querySelector('.lr-fact-link');assert.equal(context.dataset.fact,r.fields.uniqueness_fact_id.fact_id);}
    if(name==='dependent'&&part.textContent.includes('y ∈ B')){assert(tail.textContent.includes('0 ∈ R'),'later value domains use the actual earlier value');assert(!tail.textContent.includes('0 ∈ B'));}
    if(['have-exist','have-comparison'].includes(name)){
     const sourceStep=part.querySelector('.lr-proof-step');await expand(sourceStep);const search=d.resolve(d.resolve(r.fields.verify_exist).fields.searched_proof);if(search.variant==='ByKnownExistShapedFact')assert(sourceStep.querySelector('.lr-fact-link'),'a known existential retains its actual source citation');else assert(sourceStep.querySelector('.lr-proof-application'),'a builtin existential retains its actual rule rather than borrowing an earlier existence statement');
     const body=s.line+1;await v.close();const bodyCard=await v.hover(body);assert(bodyCard.querySelector('.lr-introduction-proof'));assert(!bodyCard.textContent.includes(locale==='zh'?'在当前证明中假定':'assumed in the current proof'),'existence-guaranteed properties are not assumptions');
    }
    if(['obtain-exist','obtain-atomic','preimage'].includes(part.dataset.route))assert(part.querySelector('.lr-witness-names'),name+':'+s.id+' '+part.textContent);
    if(part.dataset.route==='preimage')assert(part.querySelector('.lr-witness-names').textContent.includes(locale==='zh'?'函数的形式输入参数':"function's formal input parameters"));
    if(name==='preimage-returned'&&part.textContent.includes('actual'))assert(part.textContent.includes('shifted(2)(actual)'),'returned-function preimages retain both argument groups');
    if(name==='preimage-field'&&part.dataset.route==='preimage')assert(part.textContent.includes('ops.op(a)'),'the actual callable field is preserved');
    if(name==='local'&&!s.scope_id.startsWith('file:'))assert(card.querySelector('.lr-proof-context').textContent.includes(locale==='zh'?'当前局部范围':'current local scope'),'a local calculation scope does not invent assumptions');
    if(name==='preimage-field'&&part.dataset.route==='equal'){
     const automatic=r.fields.auto_opened_struct_layers.flatMap(layer=>d.resolve(layer).fields.store_and_infer),ids=automatic.map(value=>(d.result(d.resolve(value).fields.store).fields.fact_id).fact_id),disclosure=part.querySelector('.lr-auto-struct-properties');assert(disclosure&&!disclosure.open,'automatic structure properties start collapsed');assert.deepEqual(disclosure.querySelectorAll('.lr-fact-link').map(link=>link.dataset.fact),ids);await disclosure.querySelector('summary').click();assert(disclosure.textContent.includes('ops.op ∈ fn'));
     const toggle=v.row(s.line).querySelector('.lr-inference-toggle');assert(toggle);const shown=JSON.parse(toggle.dataset.facts);assert(shown.length);const temporaryScope=d.resolve(r.fields.type_local_env).scope_id,temporary=b.facts.filter(f=>f.scope_id===temporaryScope&&f.inference_ids?.length);assert(temporary.length);assert(temporary.every(f=>!shown.includes(f.id)),'preflight structure inferences never appear as actual consequences');assert(shown.every(id=>b.facts.find(f=>f.id===id).scope_id===s.scope_id),'structure consequences retain the actual declaration scope');assert(disclosure.querySelector('.lr-struct-definition-link'));
    }
    await v.close();checked++;
   }v.done();
  }
  for(const name of ['equal','have-comparison']){
   const b=fixture(name),d=records(b),v=mount(b,locale),s=introductions(b)[0],r=d.result(s.evidence),aggregate=d.resolve(r.fields.store_and_infer_result),stored=new Set(aggregate.fields.stored_fact_ids.map(value=>value.fact_id)),inferred=b.facts.filter(f=>stored.has(f.id)&&f.inference_ids?.length);assert(inferred.length,'the real declaration has actual inferred consequences');
   for(const fact of inferred){const line=name==='have-comparison'?s.line+1:s.line,toggle=v.row(line).querySelector('.lr-inference-toggle');assert(toggle);assert(JSON.parse(toggle.dataset.facts).includes(fact.id),'a declaration inference remains at the exact native type/body store anchor');}
   if(name==='have-comparison')assert(!v.row(s.line).querySelector('.lr-inference-toggle'),'body consequences do not move to the declaration header');v.done();
  }
  const b=fixture('obtain-exist'),d=records(b),v=mount(b,locale),s=introductions(b)[1],card=await v.hover(s.line),part=card.querySelector('.lr-introduction-proof');assert(part.textContent.includes(locale==='zh'?'唯一':'exactly one'));assert(part.querySelectorAll('.lr-introduction-properties .lr-fact-link').length>=3,'unique existence also introduces its actual uniqueness forall');const link=part.querySelector('.lr-introduction-properties .lr-fact-link'),id=link.dataset.fact;await link.click();assert.equal(v.reader.getSelection().fact,id);assert.equal(v.reader.getSelection().focusLine,s.line);assert(v.root.querySelector('.lr-detail-body .lr-introduction-proof'));await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().statement,s.id);v.done();
  const repeated=fixture('repeated'),data=records(repeated),rv=mount(repeated,locale),same=introductions(repeated).filter(s=>s.source_statement_id==='statement2');assert.equal(same.length,2);await rv.row(same[0].line).querySelector('.lr-line-number').click();
  for(const [index,s] of same.entries()){
   await rv.root.querySelectorAll('.lr-contexts .lr-chip')[index].click();await rv.close();const c=await rv.hover(s.line),ids=propertyIds(c),r=data.result(s.evidence),expected=outputRoots(data,r);assert.deepEqual(ids,expected);assert(ids.every(id=>!outputRoots(data,data.result(same[1-index].evidence)).includes(id)),'base and step declarations retain separate actual properties');const published=new Set(data.resolve(r.fields.store_and_infer_result).fields.stored_fact_ids.map(value=>value.fact_id)),inferred=repeated.facts.filter(f=>published.has(f.id)&&f.inference_ids?.length),toggle=rv.row(s.line).querySelector('.lr-inference-toggle');assert(inferred.length&&toggle);assert(inferred.every(f=>JSON.parse(toggle.dataset.facts).includes(f.id)),'the selected execution retains its own real inferences');await rv.close();
   const letInstances=introductions(repeated).filter(candidate=>candidate.statement_kind.endsWith('LetObjStmt')),alias=letInstances.find(candidate=>candidate.scope_id===s.scope_id);assert(alias);const target=rv.row(alias.line).querySelectorAll('[data-symbol]').find(token=>token.textContent==='a');await rv.move(target);const card=rv.root.querySelector('.lr-proof-popover'),button=card.querySelector('.lr-proof-symbol .lr-introduction-link');assert(button);await button.click();assert.equal(rv.reader.getSelection().statement,s.id,'symbol evidence uses the selected execution scope');await rv.close();await rv.row(s.line).querySelector('.lr-line-number').click();
  }rv.done();
 }
 for(const name of ['let-zero','let-duplicate','let-undefined','have-empty','have-undefined','equal-negative','equal-count','have-exist-false','have-exist-undefined','obtain-false','obtain-count','atomic-type','atomic-nonexistential','preimage-target','preimage-count','replacement-arity','replacement-unknown']){
  const b=fixture(name),v=mount(b,'en');assert.equal(b.run_result,'failure');for(const s of b.statements.filter(s=>s.status==='rejected'&&leaves.has(s.statement_kind?.split('.').at(-1)))){const card=await v.hover(s.line);assert(card?.querySelector('.lr-failure-summary'));assert(!card.querySelector('.lr-introduction-proof'),'a rejected introduction has no successful properties');await v.close();}for(const issue of b.diagnostics.filter(issue=>issue.phase==='parse'&&issue.line)){const card=await v.hover(issue.line);assert(card?.querySelector('.lr-failure-summary'));assert(!card.querySelector('.lr-introduction-proof'),'a parse rejection cannot acquire a successful introduction');await v.close();}v.done();
 }
 for(const kind of ['store','existence','projection','name','kind','position','producer','legacy']){
  const b=fixture('obtain-atomic'),d=records(b),s=introductions(b)[0],r=d.result(s.evidence),declaration=d.resolve(r.fields.statement);
  if(kind==='store')delete r.fields.store_and_infer_result;
  if(kind==='existence')delete r.fields.verify_atomic;
  if(kind==='projection')delete r.fields.projected_exist;
  if(kind==='name')declaration.fields.equal_tos=[{kind:'symbol_reference',symbol_id:'builtin:set:R',name:'R'}];
  if(kind==='kind')s.statement_kind='Definition.DefineObj.FutureObject';
  if(kind==='position')declaration.fields.line_file.line=1;
  if(kind==='producer')for(const id of outputRoots(d,r))b.facts.find(f=>f.id===id).producer_statement_id='statement0';
  if(kind==='legacy')for(const statement of b.statements)delete statement.declaration_symbol_ids;
  const v=mount(b,'en'),card=await v.hover(s.line),part=card?.querySelector('.lr-introduction-proof');
  if(['name','kind','position'].includes(kind))assert(!part,'conflicting source identity cannot acquire an introduction');else{assert(part);if(kind!=='legacy')assert(/incomplete|not fully exported/.test(part.textContent),kind+' '+part.textContent);if(['store','producer'].includes(kind)){assert.equal(propertyIds(part).length,0);assert(!v.row(s.line).textContent.includes('Properties obtained 0'));}if(kind==='projection')assert(!part.querySelector('.lr-witness-names'),'missing projected existentials are not reconstructed from nearby definitions');}v.done();
 }
 for(const kind of ['signature','wrong-property','unknown-route','parameters']){
  const b=fixture('preimage'),d=records(b),s=introductions(b).find(s=>s.statement_kind.endsWith('HaveByPreimageStmt')),r=d.result(s.evidence),selection=d.resolve(r.fields.signature_selection);
  if(kind==='signature')delete r.fields.signature_selection;
  if(kind==='wrong-property')selection.fields.fact_id={kind:'fact_reference',fact_id:outputRoots(d,r)[0]};
  if(kind==='unknown-route')selection.variant='FutureInterface';
  if(kind==='parameters')delete r.fields.preimage_parameters;
  const v=mount(b,'en'),card=await v.hover(s.line);assert(!card.querySelector('.lr-witness-names'));assert(/incomplete|not fully exported/.test(card.textContent));v.done();
 }
 for(const kind of ['missing','wrong-object','future']){
  const b=fixture('preimage-field'),d=records(b),s=introductions(b).find(s=>s.statement_kind.endsWith('HaveObjEqualStmt')),r=d.result(s.evidence),base=d.resolve(r.fields.store_and_infer_result).fields.store_and_infer_results.map(value=>d.result(d.resolve(value).fields.store).fields.fact_id.fact_id);
  if(kind==='missing')delete r.fields.auto_opened_struct_layers;
  if(kind==='wrong-object')d.resolve(r.fields.auto_opened_struct_layers[0]).fields.obj={type:'Obj',variant:'Identifier',fields:{'0':{kind:'symbol_reference',symbol_id:'builtin:set:R',name:'R'}},text:'R'};
  if(kind==='future')d.resolve(r.fields.auto_opened_struct_layers[0]).type='FutureStructLayer';
  const v=mount(b,'en'),card=await v.hover(s.line);assert.deepEqual(propertyIds(card),base,'unknown automatic layers cannot add guessed structure properties');assert(!card.querySelector('.lr-auto-struct-properties'));assert(card.textContent.includes('complete record is missing'));v.done();
 }
 if(process.argv[3]){
  const exported=path.resolve(process.argv[3]),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),data=records(whole);assert.equal(whole.sources.length,3);
  for(const locale of ['zh','en']){
   const manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'),'utf8')),dom=createDOM(),root=dom.root(),timers=new Map(),reads=[];let serial=0;
   const fetch=async url=>{const target=new URL(url);assert.equal(target.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(target.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
   vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale});
   for(const source of whole.sources){
    const s=introductions(whole).find(s=>s.source_id===source.id&&(!source.path.includes('witnesses')||s.statement_kind.endsWith('ObtainObjFromAtomicFact')));assert(s);await reader.selectStatement(s.id);const selected=root.querySelector('.lr-detail-body .lr-introduction-proof');assert(selected,source.path+': selected native introduction '+root.querySelector('.lr-detail-body').textContent);await root.trigger('keydown',{key:'Escape'});const row=root.querySelector('[data-line="'+s.line+'"]');await row.querySelector('.lr-source-code').trigger('pointermove');for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card?.querySelector('.lr-introduction-proof'),source.path+': native source-row preview');assert.deepEqual(propertyIds(card),outputRoots(data,data.result(s.evidence)));assert(!/f\d+::/.test(card.textContent),'captured file namespaces are displayed through resolved public names');await root.trigger('keydown',{key:'Escape'});
   }
   assert(whole.sources.every(source=>reads.some(file=>file.endsWith(manifest.sources.find(entry=>entry.id===source.id).chunk_url))),'native proof chunks load through the actual public API');reader.destroy();
  }
 }
 console.log(JSON.stringify({passed:true,checked,bilingualAndReadOnly:true,eightNativeIntroductionForms:true,existenceIsNotAnAssumption:true,actualWitnessNamesNotEqualities:true,dependentDomains:true,preimageInterfaceAndReturnedFieldCalls:true,replacementPrincipleAndUniqueness:true,actualPropertyAndSourceNavigation:true,repeatedExecutionScopes:true,wdLastAndClosed:true,failedAndMissingDataNotGuessed:true,inputRecordsUnchanged:true,actualNamespacedStaticChunks:!!process.argv[3]}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
