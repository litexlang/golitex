'use strict';
// Object/property correspondence is observed by identity, never by spelling.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node introduction-property-identities.cjs <fixtures> [reader-source]');
const code=fs.readFileSync(process.argv[3]||path.join(__dirname,'../reader.js'),'utf8');
const read=name=>JSON.parse(fs.readFileSync(path.join(directory,'intro-identity-'+name+'.json'),'utf8'));
function records(b){const nodes=new Map(b.evidence_nodes.map(row=>[row.id,row.node]));function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}function result(v){let n=resolve(v);while(n.fields?.['0'])n=resolve(n.fields['0']);return n;}return {nodes,resolve,result};}
function mount(b,locale,editable){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 const v={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row);return row;},async move(target){assert(target);if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'Native symbols, facts, scopes, statuses and source addresses remain unchanged');const source=b.sources.find(s=>s.id===(reader.getSelection().source||b.entry_source_id));assert.equal(root.querySelectorAll('.lr-code-row').length,source.content.split('\n').length);reader.destroy();}};return v;
}
const introductions=b=>b.statements.filter(s=>s.status==='accepted'&&s.statement_kind.endsWith('HaveObjByExistFactsStmt'));
function outputs(d,s){const r=d.result(s.evidence),aggregate=d.resolve(r.fields.store_and_infer_result);return aggregate.fields.store_and_infer_results.map(value=>{const store=d.result(d.resolve(value).fields.store);return (store.fields.fact_id||store.fields.whole_fact_id).fact_id;});}
function bodyIDs(d,s){const r=d.result(s.evidence),decl=d.resolve(r.fields.statement);return decl.fields.facts.map(value=>d.result(value).fields.fact_id.fact_id);}
async function run(){let checked=0,interactions=0;
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const name of ['original','outer','constant','lambda','comparison','independent','natural'])for(const mode of ['ordinary','registered']){
  const b=read(name+'-'+mode),d=records(b),v=mount(b,locale,editable);
  for(const s of introductions(b)){
   let card=await v.move(v.row(s.line).querySelector('.lr-source-code')),part=card?.querySelector('.lr-introduction-proof');assert(part,name+'-'+mode+':'+s.id);
   const missing=mode==='registered'&&['original','outer','natural'].includes(name)?bodyIDs(d,s):[];
   const unresolved=part.querySelector('.lr-introduction-unmatched-properties');
   if(missing.length){assert(unresolved,'unmatched object identities must not appear as ordinary properties');assert.equal(unresolved.open,false);assert.deepEqual(unresolved.querySelectorAll('.lr-fact-link').map(n=>n.dataset.fact),missing);assert(unresolved.querySelectorAll('.lr-fact-link').every(n=>n.dataset.correspondence==='incomplete'));assert(part.querySelector('.lr-introduction-properties').dataset.correspondence==='incomplete');}
   else assert(!unresolved,name+'-'+mode+': legitimate constants, outer objects and nested binders retain their properties');
   const ids=part.querySelectorAll('.lr-introduction-properties .lr-fact-link').map(n=>n.dataset.fact);assert.deepEqual(new Set(ids),new Set(outputs(d,s)),'every actual store remains accessible');
   const names=d.resolve(d.resolve(d.result(s.evidence).fields.statement).fields.param_def),groups=names.fields.groups.flatMap(value=>d.resolve(value).fields.params),symbol=v.row(s.line).querySelectorAll('[data-symbol]').find(n=>groups.some(g=>n.dataset.symbol===g.symbol_id));assert(symbol);
   card=await v.move(symbol);const info=card.querySelector('.lr-proof-symbol');assert(info&&!info.hidden);assert.equal(!!info.querySelector('.lr-introduction-unmatched-properties'),!!missing.length,'symbol hover cannot hide missing conditions behind its exact-ID filter');interactions++;
   if(missing.length){const link=part.querySelector('.lr-introduction-unmatched-properties .lr-fact-link');await link.click();assert.equal(v.reader.getSelection().fact,missing[0]);const selected=v.root.querySelector('.lr-detail-body .lr-introduction-unmatched-properties');assert(selected&&selected.open,'selecting the actual stored fact retains its qualification');await v.root.querySelector('.lr-back').click();assert(v.root.querySelector('.lr-detail-body .lr-introduction-proof'));interactions+=2;}
   await v.close();const bodyLine=s.line+1,bodyCard=await v.move(v.row(bodyLine).querySelector('.lr-source-code'));if(missing.length)assert(bodyCard.querySelector('.lr-introduction-unmatched-properties'),'source-body hover keeps the same identity warning');await v.close();checked++;
  }
  if(name==='natural'&&mode==='registered')for(const batch of b.inferences.filter(i=>introductions(b).some(s=>s.id===i.producer_statement_id))){
   const actual=b.facts.find(f=>f.id===batch.fact_ids[0]);await v.reader.selectFact(actual.id);const inference=v.root.querySelector('.lr-detail-body .lr-inference-proof');assert(inference,'an actual inferred consequence retains its own proof');const seed=inference.querySelector('.lr-fact-link');assert.equal(seed.dataset.fact,batch.source_fact_id);assert.equal(seed.dataset.correspondence,'incomplete','inference provenance cannot bypass the source-property qualification');await seed.click();assert.equal(v.reader.getSelection().fact,batch.source_fact_id);assert(v.root.querySelector('.lr-detail-body .lr-introduction-unmatched-properties'));await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().fact,actual.id);assert(v.root.querySelector('.lr-detail-body .lr-inference-proof [data-correspondence="incomplete"]'));await v.close();interactions+=3;
  }
  for(const s of b.statements.filter(s=>s.status==='rejected'&&s.statement_kind.endsWith('HaveObjByExistFactsStmt'))){const card=await v.move(v.row(s.line).querySelector('.lr-source-code'));assert(!card.querySelector('.lr-introduction-proof'),'an actual rejected introduction has no successful properties');await v.close();checked++;}
  v.done();
 }
 for(const locale of ['zh','en'])for(const editable of [true,false]){
  const b=read('external-registered'),d=records(b),s=introductions(b)[0],v=mount(b,locale,editable);assert.equal(b.sources.length,2);assert.equal(b.run_result,'success');await v.reader.selectStatement(s.id);await v.close();const card=await v.move(v.row(s.line).querySelector('.lr-source-code')),part=card.querySelector('.lr-introduction-proof');assert(part&&!part.querySelector('.lr-introduction-unmatched-properties'),'an exact imported declaration is a valid free-object correspondence');assert.deepEqual(new Set(part.querySelectorAll('.lr-introduction-properties .lr-fact-link').map(n=>n.dataset.fact)),new Set(outputs(d,s)));v.done();checked++;
 }
 // Missing declaration metadata is a data control, not a new mathematical run.
 for(const control of ['free-symbol','foreign-owner','unrelated-parameter','builtin-metadata','missing-subject','nested-binder','legacy']){
  const b=read(control==='nested-binder'?'lambda-ordinary':'outer-ordinary'),d=records(b),s=introductions(b)[0],body=bodyIDs(d,s)[0];
  let id;if(['free-symbol','foreign-owner','unrelated-parameter'].includes(control))id=b.symbols.find(n=>n.name==='reading_outside').id;
  if(control==='builtin-metadata')id=b.symbols.find(n=>n.name==='R').id;
  if(control==='nested-binder')id=b.symbols.find(n=>n.name==='t').id;
  const remove=control==='nested-binder'?b.symbols.filter(n=>n.name==='t').map(n=>n.id):id?[id]:[];
  for(const id of remove){b.occurrences=b.occurrences.filter(n=>n.symbol_id!==id||!n.definition);for(const statement of b.statements)if(statement.declaration_symbol_ids)statement.declaration_symbol_ids=statement.declaration_symbol_ids.filter(v=>v!==id);const symbol=b.symbols.find(n=>n.id===id);delete symbol.definition_statement_id;if(control==='builtin-metadata')delete symbol.kind;}
  if(control==='foreign-owner')b.symbols.find(n=>n.id===id).definition_statement_id=s.id;
  if(control==='unrelated-parameter')b.evidence_nodes.push({id:'data-control-unrelated-parameter',node:{type:'TypedParameterGroup',fields:{params:[{kind:'symbol_reference',symbol_id:id,name:'reading_outside'}],param_type:{type:'ParamType',variant:'Set'}}}});
  if(control==='legacy')for(const s of b.statements)delete s.declaration_symbol_ids;
  if(control==='missing-subject'){for(const node of d.nodes.values())if(node.type==='Obj'&&node.variant==='Identifier'&&d.result(node).name==='reading_outside')node.fields['0']={kind:'unavailable'};}
  const v=mount(b,'en',true),card=await v.move(v.row(s.line).querySelector('.lr-source-code')),part=card.querySelector('.lr-introduction-properties');assert(part);
  if(control==='nested-binder')assert(!part.querySelector('.lr-introduction-unmatched-properties'),'a binder retained in this condition does not need a global declaration');else if(control==='builtin-metadata'||control==='legacy')assert(!part.querySelector('.lr-introduction-unmatched-properties'),'typed builtin constructors and actual definition occurrences remain usable');else assert(part.querySelector('.lr-introduction-unmatched-properties'),control+': missing identity authority is explicit');v.done();checked++;
 }
 console.log(JSON.stringify({passed:true,checked,interactions,bilingualEditableAndReadOnly:true,registeredProducerBoundaryPreserved:true,sourceFactSymbolAndBack:true,outerAndConstantConditions:true,nestedBinders:true,missingRecordsExplicit:true,NativeUnchanged:true,browserObserved:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
