'use strict';
// Actual tuple stores, source events and retained origin correspondence.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw Error('Usage: node tuple-coordinate-inferences.cjs <fixtures> [reader-source] [qualified-export-or-json]');
const code=fs.readFileSync(process.argv[3]&&process.argv[3]!=='-'?process.argv[3]:path.join(__dirname,'../reader.js'),'utf8');
const rule='infer.InferEqualFactResult::TupleCoordinates';
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'tuple-coordinate-'+name+'.json')));
function records(bundle){
 const nodes=new Map(bundle.evidence_nodes.map(row=>[row.id,row.node]));
 function resolve(value){const seen=new Set();while(value?.kind==='evidence_reference'&&!seen.has(value.evidence_id)){seen.add(value.evidence_id);value=nodes.get(value.evidence_id);}return value||{};}
 function result(value){let node=resolve(value);const seen=new Set();while(node.fields?.['0']&&!seen.has(node)){seen.add(node);node=resolve(node.fields['0']);}return node;}
 function walk(value,fn){const pending=[value],seen=new Set();while(pending.length){const node=resolve(pending.pop());if(!node||typeof node!=='object'||seen.has(node))continue;seen.add(node);fn(node);pending.push(...(Array.isArray(node)?node:Object.values(node)));}}
 return {nodes,resolve,result,walk};
}
function items(bundle){
 const d=records(bundle),found=[];
 for(const batch of bundle.inferences.filter(batch=>batch.rule_ids.includes(rule))){
  const details=[];d.walk(batch.evidence,node=>{if(node.type==='InferEqualFactTupleCoordinatesResult')details.push(node);});
  for(const detail of details){
   const seed=d.resolve(detail.fields.source_fact_id).fact_id,equal=[...d.nodes.values()].find(node=>node.type==='EqualFact'&&node.fields.fact_id?.fact_id===seed),tuple=d.result(detail.fields.reversed?equal.fields.left:equal.fields.right),producer=bundle.statements.find(s=>s.id===batch.producer_statement_id);
   detail.fields.coordinates.forEach((value,index)=>{const entry=d.resolve(value),stored=d.result(entry.fields.store),id=d.resolve(stored.fields.fact_id).fact_id,fact=bundle.facts.find(f=>f.id===id);assert(fact);found.push({batch,detail,entry,stored,equal,tuple,fact,producer,index:index+1,dimension:tuple.fields.args.length,line:equal.fields.line_file.source_id===producer.source_id?equal.fields.line_file.line:producer.line});});
  }
 }
 return found;
}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 return {...dom,root,reader,async hover(target,keyboard=false){if(keyboard)await target.trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger(target.classList.contains('lr-inference-toggle')?'mouseenter':'pointermove');for(let round=0;round<3;round++)for(const [id,fn]of [...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},done(){assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources.find(s=>s.id===reader.getSelection().source).content.split('\n').length);assert.equal(JSON.stringify(bundle),before,'source, Native stores and scope identities stay unchanged');reader.destroy();}};
}
function retained(root,item,locale){
 const part=root.querySelector('.lr-inference-proof'),row=part?.querySelector('.lr-tuple-coordinate-inference');assert(part&&row,item.fact.text);assert.equal(row.dataset.status,'retained',item.fact.text);assert.equal(row.dataset.rule,rule);assert.equal(row.dataset.coordinate,String(item.index));assert.equal(row.dataset.dimension,String(item.dimension));assert.equal(row.dataset.orientation,item.detail.fields.reversed?'reversed':'forward');assert.equal(part.dataset.fact,item.fact.id);assert.equal(part.dataset.scope,item.fact.scope_id);assert.equal(part.dataset.sourceFact,item.batch.source_fact_id);assert(row.textContent.includes(locale==='zh'?'坐标从 1 开始编号':'Coordinates are numbered from 1'));assert(!row.textContent.includes(locale==='zh'?'数学说明尚未提供':'not yet available'));assert(part.querySelector('[data-fact="'+item.batch.source_fact_id+'"]'));assert(!part.querySelector('.lr-equivalence'),'a projected coordinate is a one-way consequence');return part;
}
async function openInline(view,item){
 await view.reader.selectStatement(item.producer.id,item.line);await view.root.trigger('keydown',{key:'Escape'});
 const row=view.root.querySelector('[data-line="'+item.line+'"]'),toggle=row?.querySelectorAll('.lr-inference-toggle').find(node=>JSON.parse(node.dataset.facts).includes(item.fact.id));assert(toggle,'actual coordinate belongs beside its producing source row');
 await view.hover(toggle);const list=view.root.querySelector('.lr-inferred-facts');assert(list&&!list.open,'inferred consequences start closed: '+item.fact.text+' / '+item.producer.id);await toggle.click();await list.querySelector('summary').click();const result=list.querySelector('[data-fact="'+item.fact.id+'"]');assert(result);await result.click();assert.equal(view.reader.getSelection().fact,item.fact.id);assert.equal(view.reader.getSelection().focusLine,item.line);
}
async function run(){
 let checked=0;
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const name of ['public','direct','symbolic','reversed','conjunction','nested-step','failed-scope','singleton']){
  const bundle=fixture(name),view=mount(bundle,locale,editable),actual=items(bundle);assert(actual.length,name);
  for(const item of actual){
   try{await openInline(view,item);}catch(error){error.message=name+'/'+locale+'/'+editable+': '+error.message;throw error;}let part=retained(view.root.querySelector('.lr-detail-body'),item,locale);const snapshot=JSON.parse(JSON.stringify(view.reader.getSelection()));
   await part.querySelector('[data-fact="'+item.batch.source_fact_id+'"]').click();assert.equal(view.reader.getSelection().fact,item.batch.source_fact_id);await view.root.querySelector('.lr-back').click();assert.deepEqual(JSON.parse(JSON.stringify(view.reader.getSelection())),snapshot);part=retained(view.root.querySelector('.lr-detail-body'),item,locale);
   if(name==='conjunction'){const component=part.querySelector('.lr-inference-conjunct .lr-fact-link');assert(component);assert.equal(component.dataset.fact,item.detail.fields.source_fact_id.fact_id);}
   if(name==='failed-scope'){const parent=bundle.statements.find(s=>s.status==='rejected'&&s.statement_kind.endsWith('ClaimStmt'));assert.equal(bundle.run_result,'failure');assert(parent);assert.notEqual(item.fact.scope_id,parent.scope_id);assert(!parent.produced_fact_ids.includes(item.fact.id),'local coordinates are not published by the failed claim');}
   checked++;
  }
  if(name==='direct'){
   await view.root.trigger('keydown',{key:'Escape'});const card=await view.hover(view.root.querySelector('[data-line="2"] .lr-source-code'));assert(card);const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);const ids=card.querySelectorAll('.lr-fact-link').map(link=>link.dataset.fact);assert(actual.every(item=>ids.includes(item.fact.id)),'the later sum actually cites both stored coordinate equalities');const chosen=actual[0];await card.querySelector('[data-fact="'+chosen.fact.id+'"]').click();retained(view.root.querySelector('.lr-detail-body'),chosen,locale);await view.root.querySelector('.lr-back').click();assert.equal(view.reader.getSelection().focusLine,2);checked++;
  }
  if(editable){const input=view.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(view.root.querySelectorAll('.lr-inference-toggle,.lr-proof-popover,.lr-inference-popover').length,0,'editing clears old semantic results');}view.done();
 }
 for(const name of ['nested-boundary','alias-boundary','empty']){
  const b=fixture(name),actual=items(b);if(name==='empty')assert.equal(actual.length,0);else{assert.equal(actual.length,2);if(name==='nested-boundary')assert(actual.every(item=>!item.fact.text.includes('pair(1)(')),'the next tuple layer is not inferred without a new seed');else assert(actual.every(item=>item.producer.line===1),'an alias does not recursively project another object');}const v=mount(b,'en');if(name==='empty')assert.equal(v.root.querySelectorAll('.lr-inference-toggle').length,0);v.done();checked++;
 }
 for(const name of ['wrong-coordinate','index-zero','index-outside']){
  const b=fixture(name);assert.equal(b.run_result,'failure');const rejected=b.statements.find(s=>s.status==='rejected');assert(rejected);assert.equal(rejected.produced_fact_ids.length,0);assert.equal(items(b).length,2,'previously accepted coordinates survive the rejection');const v=mount(b,'en');await v.reader.selectStatement(rejected.id,rejected.line);assert(!v.root.querySelector('.lr-detail-body .lr-tuple-coordinate-inference'));v.done();checked++;
 }
 for(const control of ['seed','orientation','length','order','duplicate','index','value','subject','source-line','source-file','stored-id','stored-subject','missing-store','batch-scope','producer']){
  const b=fixture('direct'),d=records(b),item=items(b)[0],f=item.detail.fields,conclusion=d.result(item.stored.fields.fact),call=d.result(conclusion.fields.left),body=call.fields.body;
  if(control==='seed')f.source_fact_id={kind:'fact_reference',fact_id:'foreign'};if(control==='orientation')f.reversed=true;if(control==='length')f.coordinates.pop();if(control==='order')f.coordinates.reverse();if(control==='duplicate')f.coordinates[1]=f.coordinates[0];if(control==='index')d.result(body.at(-1)[0]).fields.normalized_value='2';if(control==='value')conclusion.fields.right=item.tuple.fields.args[1];if(control==='subject')conclusion.fields.left=item.equal.fields.right;if(control==='source-line')conclusion.fields.line_file.line=2;if(control==='source-file')conclusion.fields.line_file.source_id='foreign';if(control==='stored-id')item.entry.stored_fact_ids=['foreign'];if(control==='stored-subject')delete item.stored.fields.fact;if(control==='missing-store')delete item.entry.fields.store;if(control==='batch-scope')item.batch.scope_id='foreign';if(control==='producer')item.batch.producer_statement_id='foreign';
  const v=mount(b,'en');await v.reader.selectFact(item.fact.id);const row=v.root.querySelector('.lr-tuple-coordinate-inference');assert(!row||row.dataset.status==='incomplete',control+' must not borrow another coordinate');if(row)assert.equal(row.dataset.coordinate,undefined);v.done();checked++;
 }
 const book=process.argv[4];if(book){
  const json=book.endsWith('.json'),exported=json?null:path.resolve(book),bundle=JSON.parse(fs.readFileSync(json?book:path.join(exported,'reading.json'))),item=items(bundle).find(value=>value.producer.source_id===bundle.sources[1].id);assert(item);assert.notEqual(item.equal.fields.line_file.source_id,item.producer.source_id,'the released equality retains its original defining source');
  for(const locale of ['zh','en']){
   const dom=createDOM(),root=dom.root(),reads=[],before=JSON.stringify(bundle),fetch=async input=>{const url=new URL(input);assert.equal(url.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(url.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return{ok:true,json:async()=>JSON.parse(fs.readFileSync(file))};};vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout,clearTimeout}));let reader;
   if(json)reader=dom.window.LitexReading.mount(root,{document:bundle,locale});else{const manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json')));manifest.entry_source_id=item.producer.source_id;reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale});}
   await reader.selectStatement(item.producer.id,item.line);const toggle=root.querySelector('.lr-inference-toggle');assert(toggle);await toggle.click();await root.querySelector('.lr-inferred-facts summary').click();await root.querySelector('.lr-inferred-result[data-fact="'+item.fact.id+'"]').click();let part=retained(root.querySelector('.lr-detail-body'),item,locale);const snapshot=JSON.parse(JSON.stringify(reader.getSelection()));assert(!/\bf\d+::/.test(part.textContent),'internal module qualifiers stay out of the prose');await part.querySelector('[data-fact="'+item.batch.source_fact_id+'"]').click();const origin=root.querySelector('.lr-expansion-proof .lr-definition-link');assert(origin);await origin.click();assert.equal(reader.getSelection().source,bundle.sources[0].id);await root.querySelector('.lr-back').click();await root.querySelector('.lr-back').click();assert.deepEqual(JSON.parse(JSON.stringify(reader.getSelection())),snapshot);retained(root.querySelector('.lr-detail-body'),item,locale);assert.equal(JSON.stringify(bundle),before);if(!json)assert(reads.length>=2);reader.destroy();checked++;
  }
  for(const control of ['declaration-source','declaration-owner','declared-symbol','parameter-name','parameter-domain','original-value']){
   const b=JSON.parse(JSON.stringify(bundle)),d=records(b),i=items(b).find(value=>value.producer.source_id===b.sources[1].id),release=d.result(i.producer.evidence),looked=d.resolve(release.fields.looked_up),definition=d.resolve(looked.fields['0'][1]),group=d.resolve(d.resolve(definition.fields.param_def).fields.groups[0]);if(control==='declaration-source')definition.declaration.source_id='foreign';if(control==='declaration-owner')definition.declaration.statement_id=i.producer.id;if(control==='declared-symbol')b.statements[0].declaration_symbol_ids=[];if(control==='parameter-name')group.fields.params[0]={...group.fields.params[0],name:'foreign'};if(control==='parameter-domain')group.fields.param_type={kind:'unavailable'};if(control==='original-value')definition.fields.objs_equal_to=[i.tuple.fields.args[0]];const v=mount(b,'en');await v.reader.selectFact(i.fact.id);const row=v.root.querySelector('.lr-tuple-coordinate-inference');assert(!row||row.dataset.status==='incomplete',control);v.done();checked++;
  }
 }
 console.log(JSON.stringify({passed:true,checked,bilingualEditableReadOnly:true,foldedSourceResults:true,actualCoordinateIndexValueOrientation:true,exactSeedNavigationAndBack:true,oneLayerEmptyAliasBoundaries:true,failedLocalNotPublished:true,missingForeignRecordsIncomplete:true,qualifiedBook:!!book,sourceAndNativeUnchanged:true,browserObserved:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
