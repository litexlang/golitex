'use strict';
// Real native definitions through the public source reader and DOM events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node function-definitions.cjs <function-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'function-'+name+'.json'),'utf8'));
const leaves=new Set(['HaveFnEqualStmt','HaveFnEqualCaseByCaseStmt','HaveFnByForallExistUniqueStmt','HaveFnByInducStmt','DefAlgoByCasesStmt','DefAlgoByInducStmt']);
const definitions=bundle=>bundle.statements.filter(s=>s.status==='accepted'&&leaves.has(s.statement_kind?.split('.').at(-1)));
function records(bundle){
 const nodes=new Map(bundle.evidence_nodes.map(row=>[row.id,row.node]));
 function resolve(value){const seen=new Set();while(value?.kind==='evidence_reference'&&!seen.has(value.evidence_id)){seen.add(value.evidence_id);value=nodes.get(value.evidence_id);}return value||{};}
 function result(value){let n=resolve(value);while(n.fields?.['0'])n=resolve(n.fields['0']);return n;}
 function execution(statement){const outer=result(statement.evidence);return outer.type.startsWith('ExecDefAlgo')?resolve(outer.fields.define_fn):outer;}
 function outputs(statement){const n=execution(statement),f=n.fields,g=resolve(f.store_and_infer_result);return (n.type==='ExecHaveFnByForallExistUniqueStmtSuccessResult'?[f.membership,f.property,f.uniqueness]:[g.fields.membership,...(g.type==='StoreHaveFnEqualAndInferResult'?[g.fields.defining_equal]:g.fields.case_defining)]).map(v=>{const store=result(resolve(v).fields.store);return (store.fields.fact_id||store.fields.whole_fact_id).fact_id;});}
 return {nodes,resolve,result,execution,outputs};
}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const view={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,line);return row;},
  async flush(){for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}},
  async move(target){if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');await view.flush();},
  async hover(line,focus=false){const row=view.row(line);if(focus){await row.querySelector('.lr-line-number').trigger('focus');await view.flush();}else await view.move(row.querySelector('.lr-source-code'));return root.querySelector('.lr-proof-popover');},
  async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'presentation preserves original source, scopes, proof records and fact identities');reader.destroy();}};
 assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length,'annotations add no source rows');return view;
}
async function expand(node){assert(node);await node.querySelector('summary').click();assert(!node.textContent.includes('cannot be matched exactly'),node.textContent);}
function propertyIds(part){return part.querySelectorAll('.lr-function-properties .lr-fact-link').map(link=>link.dataset.fact);}
function wdLast(card){const wd=card.querySelector('.lr-atomic-wd');assert(wd&&!wd.open);assert.equal(wd.parentNode.children.at(-1),wd);return wd;}
async function run(){
 let checked=0;
 for(const locale of ['zh','en'])for(const editable of [true,false]){
  const bundle=fixture('cases'),data=records(bundle),s=definitions(bundle)[0],v=mount(bundle,locale,editable),card=await v.hover(s.line,true),part=card.querySelector('.lr-function-definition');assert(part);assert.equal(part.dataset.route,'cases');assert.deepEqual(propertyIds(part),data.outputs(s));assert(!part.querySelector('.lr-function-properties').open);assert.equal(part.querySelectorAll('.lr-function-case').length,2);assert.equal(part.querySelectorAll('.lr-function-disjoint').length,1);wdLast(card);
  await expand(part.querySelector('.lr-function-disjoint'));assert(part.querySelector('.lr-function-disjoint').textContent.includes('x < 0'));assert(part.querySelector('.lr-function-disjoint .lr-proof-step'));
  const branch=await v.hover(s.line+1),bp=branch.querySelector('.lr-function-branch');assert(bp);assert(bp.querySelector('.lr-function-inputs').textContent.includes('x < 0'));assert(bp.textContent.includes('x ∈ R'));wdLast(branch);await expand(bp.querySelector('.lr-proof-step'));const cited=bp.querySelector('.lr-proof-step .lr-known-source .lr-fact-link');assert(cited,'return proof cites the actual typed input');assert.equal(bundle.facts.find(f=>f.id===cited.dataset.fact).scope_id,bp.dataset.scope);
  await branch.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert(v.root.querySelector('.lr-detail-body .lr-function-branch'));await v.close();
  let header=await v.hover(s.line);const link=header.querySelectorAll('.lr-function-properties .lr-fact-link')[1];await link.click();assert.equal(v.reader.getSelection().fact,data.outputs(s)[1]);assert.equal(v.reader.getSelection().focusLine,s.line+1,'the conditional function equation points to its actual source branch');await v.root.querySelector('.lr-back').click();assert(v.root.querySelector('.lr-detail-body .lr-function-definition'));await v.close();
  header=await v.hover(s.line);const evidence=header.querySelector('.lr-proof-evidence'),symbol=v.row(s.line).querySelectorAll('[data-symbol]').find(t=>t.textContent==='choose');await v.move(symbol);assert.strictEqual(v.root.querySelector('.lr-proof-popover .lr-proof-evidence'),evidence,'symbol compartment retains the statement proof');assert(v.root.querySelector('.lr-proof-symbol .lr-introduction-link'));await v.root.querySelector('.lr-proof-symbol .lr-introduction-link').click();assert(v.root.querySelector('.lr-detail-body .lr-function-definition'));await v.close();
  if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-logical-action,.lr-inference-toggle,.lr-proof-popover').length,0);}
  v.done();checked++;
 }
 for(const locale of ['zh','en'])for(const name of ['formula','guard','cases-multiple','unique','unique-carriers','recursive','recursive-single','algo-cases','algo-induc','local','local-family','higher-order','empty-graph','empty-return']){
  const bundle=fixture(name),data=records(bundle),v=mount(bundle,locale);
  for(const s of definitions(bundle)){
   const card=await v.hover(s.line),part=card?.querySelector('.lr-function-definition');assert(part,name+':'+s.id);assert.deepEqual(propertyIds(part),data.outputs(s),name);assert(!/not fully exported|incomplete/.test(part.textContent),name+': '+part.textContent);const wd=wdLast(card);await expand(wd);assert(!wd.textContent.includes('well-definedness proof was not fully exported'),name+': '+wd.textContent);
   if(name==='guard'){assert(!v.row(s.line).dataset.proofFacts,'a function guard is not a proved top-level source fact');assert(part.querySelector('.lr-function-interface').textContent.includes('x ≠ 0'));await expand(part.querySelector('.lr-proof-step'));assert(part.querySelector('.lr-proof-step').textContent.includes('(1 / x) ∈ R'));}
   if(name.startsWith('algo'))assert(part.querySelector('.lr-algorithm-registration'));
   if(name.startsWith('empty-')){assert(part.textContent.includes(locale==='zh'?'输入范围为空':'input domain is proved empty'));assert(!part.textContent.includes('0 ∈ {}'),'vacuous return typing does not establish a false ordinary membership');}
   if(part.dataset.route==='recursive'){assert(part.textContent.includes(locale==='zh'?'严格减小':'strictly decrease'));assert(part.textContent.includes('∈ Z'));assert(!part.querySelector('.lr-function-restriction').open);}
   for(const item of part.querySelectorAll('.lr-function-case'))await expand(item);
   for(const nested of part.querySelectorAll('.lr-function-case'))if(!nested.open)await expand(nested);
   for(const branch of part.querySelectorAll('.lr-function-branch'))assert(!/incomplete|not fully exported/.test(branch.textContent),branch.textContent);
   checked++;
  }
  v.done();
 }
 const unique=fixture('unique-carriers'),uv=mount(unique,'en'),us=definitions(unique)[0];const goal=await uv.hover(us.line+1);assert(goal.querySelector('.lr-proof-step'));assert(goal.textContent.includes('unique')||goal.textContent.includes('exactly one'));uv.done();
 for(const locale of ['zh','en']){
  const b=fixture('recursive'),d=records(b),v=mount(b,locale),s=definitions(b).find(s=>b.sources[0].content.split('\n')[s.line-1].includes('nested_count')),ids=d.outputs(s);
  for(const[index,line]of [[1,s.line+1],[2,s.line+3],[3,s.line+4]]){await v.reader.selectStatement(s.id);await v.close();const card=await v.hover(s.line),link=card.querySelectorAll('.lr-function-properties .lr-fact-link').find(link=>link.dataset.fact===ids[index]);assert(link);await link.click();assert.equal(v.reader.getSelection().focusLine,line,'a flattened conditional equation keeps its exact nested source leaf');await v.close();}
  const card=await v.hover(s.line+4),branch=card.querySelector('.lr-function-branch');assert(branch);assert(branch.querySelectorAll('.lr-proof-context').some(node=>node.textContent.includes('n ≥ 1')),'the nested source leaf retains its enclosing case');assert(branch.querySelectorAll('.lr-function-inputs').find(node=>node.dataset.scope===branch.dataset.scope).textContent.includes('n ≠ 1'));assert(branch.querySelector('.lr-proof-step').textContent.includes('nested_count'));v.done();checked++;
 }
 for(const name of ['wrong-codomain','wrong-call','ill-defined','missing-case','case-codomain','false-unique','nondecreasing','bad-base','algo-coverage','algo-result','algo-base','algo-recursion','empty-graph','empty-return']){
  const b=fixture(name),v=mount(b,'en');assert.equal(b.run_result,'failure');const failed=b.statements.find(s=>s.status==='rejected');assert(failed,name);const card=await v.hover(failed.line);assert(card,name);assert(!card.querySelector('.lr-function-definition'),'rejection has no successful definition explanation');v.done();checked++;
 }
 {const b=fixture('ordinary-existence'),v=mount(b,'en');assert.equal(b.run_result,'failure');assert(b.diagnostics.some(d=>d.phase==='parse'),'ordinary exist is rejected by the parser before the function Stmt');assert.equal(definitions(b).length,0);assert(!v.root.querySelector('.lr-function-definition'));v.done();checked++;}
 for(const control of ['body','return','return-domain','coverage','wrong-coverage','disjoint','missing-pair','wrong-pair','wrong-pair-proof','case-scope','stores','store-identity','name','source','algorithm']){
  const name=control==='algorithm'?'algo-cases':['body','return','return-domain'].includes(control)?'guard':'cases',b=fixture(name),d=records(b),s=definitions(b)[0],outer=d.result(s.evidence),n=d.execution(s),f=n.fields;
  if(control==='body')delete f.anonymous_fn_well_defined;
  if(control==='return'){const body=[...d.nodes.values()].find(n=>n.type==='AnonymousFnObjWellDefinedProof');delete body.fields.body_in_ret_set;}
  if(control==='return-domain'){const body=[...d.nodes.values()].find(n=>n.type==='AnonymousFnObjWellDefinedProof'),proof=d.result(body.fields.body_in_ret_set),fact=d.result(proof.fields.fact),domain=[...d.nodes].find(([id,n])=>n.type==='Obj'&&n.text==='C');assert(domain);fact.fields.set={kind:'evidence_reference',evidence_id:domain[0]};}
  if(control==='coverage')delete f.coverage;
  if(control==='wrong-coverage')d.resolve(f.coverage).fields.coverage_check=d.resolve(f.case_return_checks[0]).fields.body_in_ret_set;
  if(control==='disjoint')delete f.disjoint;
  if(control==='missing-pair')f.disjoint=[];
  if(control==='wrong-pair')d.resolve(f.disjoint[0]).fields.j='0';
  if(control==='wrong-pair-proof')d.resolve(f.disjoint[0]).fields.negated_component=d.resolve(f.case_return_checks[0]).fields.body_in_ret_set;
  if(control==='case-scope')delete d.resolve(f.case_return_checks[0]).fields.local_env;
  if(control==='stores')delete d.resolve(f.store_and_infer_result).fields.case_defining;
  if(control==='store-identity')d.resolve(f.store_and_infer_result).fields.membership_fact_id={kind:'fact_reference',fact_id:'unknown'};
  if(control==='name')d.resolve(f.statement).fields.name={kind:'symbol_reference',name:'other',symbol_id:'unknown'};
  if(control==='source')d.resolve(f.statement).fields.line_file.line++;
  if(control==='algorithm')delete outer.fields.define_fn;
  const v=mount(b,'en'),card=await v.hover(s.line),part=card?.querySelector('.lr-function-definition');
  if(['name','source'].includes(control))assert(!part,'conflicting source identities cannot borrow another definition');
  else {assert(part,control);assert(/incomplete|not fully exported/.test(part.textContent),control+': '+part.textContent);}
  v.done();checked++;
 }
 const template=fixture('template'),tv=mount(template,'en');assert(!definitions(template).length,'the template has no separately exported function Stmt');const owner=template.statements.find(s=>s.statement_kind.endsWith('DefTemplateStmt'));assert(owner);assert(!tv.row(owner.line).querySelector('[data-logical-kind="function-definition"]'),'the template header is not relabelled as a function definition');for(const annotation of tv.root.querySelectorAll('[data-logical-kind="function-definition"]')){const row=annotation.closest('.lr-code-row');assert.equal(row.dataset.statement,owner.id,'body checks remain owned by the original template source statement');assert(Number(row.dataset.line)>owner.line,'body checks are at their actual nested source position');}tv.done();
 if(process.argv[3]){
  const exported=path.resolve(process.argv[3]),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),data=records(whole);assert.equal(whole.sources.length,6);assert.equal(whole.run_result,'failure','keep the independently observed namespace-eval failure');assert(whole.statements.filter(s=>s.status==='rejected').every(s=>s.statement_kind==='Command.EvalStmt'));
  for(const locale of ['zh','en']){
   const manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'),'utf8')),dom=createDOM(),root=dom.root(),timers=new Map(),reads=[];let serial=0;
   const fetch=async url=>{const target=new URL(url);assert.equal(target.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(target.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
   vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale});
   for(const source of whole.sources){const s=definitions(whole).find(s=>s.source_id===source.id);assert(s);await reader.selectStatement(s.id);assert(root.querySelector('.lr-detail-body .lr-function-definition'),source.path);await root.trigger('keydown',{key:'Escape'});const row=root.querySelector('[data-line="'+s.line+'"]');await row.querySelector('.lr-source-code').trigger('pointermove');for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card?.querySelector('.lr-function-definition'),source.path);assert.deepEqual(propertyIds(card),data.outputs(s));assert(!/f\d+::/.test(card.textContent),'resolved source names replace internal file prefixes');assert(root.querySelector('.lr-book-heading').textContent.includes(locale==='zh'?'本次检查未通过':'Last check failed'),'accepted definition views never turn the failed overall run into a success');await root.trigger('keydown',{key:'Escape'});}
   assert(whole.sources.every(source=>reads.some(file=>file.endsWith(manifest.sources.find(entry=>entry.id===source.id).chunk_url))),'all six native proof chunks load through the public API');reader.destroy();
  }
 }
 console.log(JSON.stringify({passed:true,checked,bilingualEditableAndReadOnly:true,sixNativeForms:true,actualInputAndReturnDomains:true,coverageAndDisjointness:true,nestedRecursion:true,algorithmRegistrationNotEvaluation:true,uniqueExistenceProperties:true,exactSourceAndPropertyNavigation:true,wdLastAndClosed:true,missingAndRejectedNotGuessed:true,nativeRecordsUnchanged:true,templateOwnershipPreserved:true,actualNamespacedStaticChunks:!!process.argv[3]}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
