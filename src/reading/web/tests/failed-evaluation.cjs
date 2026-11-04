'use strict';
// Typed eval failures describe computation, independently of proposition search.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw Error('Usage: node failed-evaluation.cjs <fixtures> [reader-source]');
const code=fs.readFileSync(process.argv[3]||path.join(__dirname,'../reader.js'),'utf8');
const cases={
 'unsupported-set':'UnsupportedExpression','unsupported-object':'UnsupportedExpression',
 'power-limit':'EvaluationFailed','unknown-function':'AlgoDispatchFailed',
 'recursion-limit':'DepthExceeded','aggregate-budget':'AggregateBudgetExceeded',
 'aggregate-nested-budget':'AggregateBudgetExceeded','aggregate-range':'AggregateRangeOverflow',
 'division-wd':'WellDefined','argument-wd':'WellDefined','aggregate-wd':'WellDefined',
 'captured':'UnsupportedExpression'
};
const read=name=>{const prefixed=path.join(directory,'eval-failure-'+name+'.json');return JSON.parse(fs.readFileSync(fs.existsSync(prefixed)?prefixed:path.join(directory,name+'.json'),'utf8'));};
const owner=b=>b.statements.find(s=>s.statement_kind==='Command.EvalStmt');
function records(b){const nodes=new Map(b.evidence_nodes.map(row=>[row.id,row.node]));const resolve=value=>{const seen=new Set();while(value?.kind==='evidence_reference'&&!seen.has(value.evidence_id)){seen.add(value.evidence_id);value=nodes.get(value.evidence_id);}return value||{};};return{nodes,resolve};}
function mount(b,locale,editable){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 return{...dom,root,reader,row(line){return root.querySelector('[data-line="'+line+'"]');},async hover(line,target=null,keyboard=false){const row=this.row(line);assert(row);target||=row.querySelector('.lr-source-code');if(keyboard)await row.querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'presentation never changes Native source, scopes, evidence or publication');reader.destroy();}};
}
async function inspect(name,locale,editable){
 const b=read(name),s=owner(b),v=mount(b,locale,editable),rows=v.root.querySelectorAll('.lr-code-row').length;
 assert.equal(b.run_result,'failure');assert.equal(s.status,'rejected');
 let card=await v.hover(s.line),part=card?.querySelector('.lr-evaluation-failure');assert(part,name+': missing eval failure explanation');assert.equal(part.dataset.status,'stage-retained',part.textContent);assert.equal(part.dataset.stage,cases[name]);assert.equal(part.dataset.statement,s.id);
 assert(part.textContent.includes(locale==='zh'?'求值未完成':'Evaluation unfinished'));
 assert(!part.textContent.includes('The current proof has not established this conclusion'));assert(!part.textContent.includes('当前证明尚未建立这个结论'));
 assert(!part.querySelector('.lr-evaluation-proof,.lr-proof-substitutions,.lr-theorem-conclusions'),'no invented value, bindings or conclusions');
 if(cases[name]==='WellDefined'){
  const tail=part.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);assert(!part.querySelector('.lr-wd-unproved-conditions'),'conditions stay inside the closed disclosure');await tail.querySelector('summary').click();
  const conditions=tail.querySelector('.lr-wd-unproved-conditions');assert(conditions);assert(conditions.textContent.includes(name==='division-wd'?'0 ≠ 0':'(-1) ∈ N'),conditions.textContent);
 }else{assert(!part.querySelector('.lr-atomic-wd'),'discarded WD history is not reconstructed');assert(part.querySelector('.lr-evaluation-history'));}
 if(name==='captured'){assert(card.querySelector('.lr-proof-context'));assert(card.textContent.includes(locale==='zh'?'所在范围':'Enclosing scope'),card.textContent);}
 await card.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert.equal(v.reader.getSelection().focusLine,s.line);assert.equal(v.reader.getSelection().fact,null);assert(v.root.querySelector('.lr-detail-body .lr-evaluation-failure'));assert(v.root.querySelector('.lr-inspector-title').textContent.includes(locale==='zh'?'求值未完成':'Evaluation unfinished'));if(name==='captured'){const selection=v.reader.getSelection();await v.root.querySelector('.lr-detail-body .lr-proof-context .lr-math-link').click();assert.equal(v.reader.getSelection().statement,b.scopes.find(scope=>scope.id===s.scope_id).statement_id);await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),selection);assert(v.root.querySelector('.lr-detail-body .lr-evaluation-failure'));}await v.close();
 const keyword=v.row(s.line).querySelector('[data-keyword="eval"]');assert(keyword);card=await v.hover(s.line,keyword);assert(card.querySelector('.lr-evaluation-failure'));assert(card.querySelector('.lr-proof-symbol').textContent.includes('eval'));
 const symbol=v.row(s.line).querySelector('[data-symbol]');if(symbol){const retained=card.querySelector('.lr-evaluation-failure');assert.equal(await v.hover(s.line,symbol),card);assert.equal(card.querySelector('.lr-evaluation-failure'),retained);assert(!card.querySelector('.lr-proof-symbol').hidden);}
 await v.close();assert((await v.hover(s.line,null,true)).querySelector('.lr-evaluation-failure'));await v.close();
 assert.equal(s.produced_fact_ids.length,0);assert.equal(s.inferred_fact_ids.length,0);assert(!v.row(s.line).querySelector('.lr-inference-toggle'));assert.equal(v.root.querySelectorAll('.lr-code-row').length,rows);
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-proof-popover,.lr-evaluation-failure,.lr-diagnostic-point'));}v.done();
}
async function run(){let checks=0;
 for(const locale of ['zh','en'])for(const editable of [false,true])for(const name of Object.keys(cases)){await inspect(name,locale,editable);checks++;}
 for(const control of ['root','command','result','type','stage','prototype','payload','reason','object','canonical','span','end','line','scope','scope-source','origin','publication','inference','tokens','legacy']){
  const b=read('division-wd'),s=owner(b),d=records(b),root=d.resolve(s.evidence),command=d.resolve(root.fields['0']),result=d.resolve(command.fields['0']),failure=d.resolve(result.fields['0']),payload=d.resolve(failure.fields['0']);
  if(control==='root')root.variant='Fact';if(control==='command')command.variant='FutureCommand';if(control==='result')result.variant='Success';if(control==='type')failure.type='FutureFailure';if(control==='stage')failure.variant='FutureStage';if(control==='prototype')failure.variant='constructor';if(control==='payload')delete failure.fields['0'];if(control==='reason')delete payload.fields.reason;if(control==='object')delete payload.fields.obj;
  if(control==='canonical')s.source_statement_id='foreign';if(control==='span')s.start_byte++;if(control==='end')s.end_byte--;if(control==='line')s.line++;if(control==='scope')s.scope_id='foreign';if(control==='scope-source')b.scopes[0].source_id='foreign';if(control==='origin')s.origin='generated';if(control==='publication')s.produced_fact_ids=['foreign'];if(control==='inference')s.inferred_fact_ids=['foreign'];if(control==='tokens')b.sources[0].tokens[0].text='let';if(control==='legacy')delete s.evidence;
  const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-evaluation-failure');if(part){assert.equal(part.dataset.status,'incomplete',control);assert(!part.querySelector('.lr-atomic-wd,.lr-proof-formula'),control);}v.done();checks++;
 }
 const diagnostic=read('unsupported-set');owner(diagnostic).failure.cause='depth_exceeded';const dv=mount(diagnostic,'en',false),dc=await dv.hover(owner(diagnostic).line);assert.equal(dc.querySelector('.lr-evaluation-failure').dataset.stage,'UnsupportedExpression','typed result owns the explanation, rather than a derived diagnostic label');dv.done();checks++;
 for(const locale of ['zh','en'])for(const editable of [false,true]){
  const b=read('success'),s=owner(b),v=mount(b,locale,editable);assert.equal(b.run_result,'success');const card=await v.hover(s.line);assert(card.querySelector('.lr-evaluation-proof'));assert(!card.querySelector('.lr-evaluation-failure'));assert(card.textContent.includes('11'));const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);await card.querySelector('.lr-proof-pin').click();const selection=v.reader.getSelection(),citation=v.root.querySelector('.lr-evaluation-citations .lr-fact-link');assert(citation);const cited=citation.dataset.fact;await citation.click();assert.equal(v.reader.getSelection().fact,cited);await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),selection);assert(v.root.querySelector('.lr-evaluation-proof'));v.done();checks++;
 }
 console.log(JSON.stringify({passed:true,checks,actualFailureVariants:new Set(Object.values(cases)).size,sourceCases:Object.keys(cases).length+1,bilingualEditableReadOnly:true,typedFailureAndSuccessfulEvaluation:true,keywordKeyboardSymbolPin:true,scopeAndEvaluationCitationBack:true,formationLastAndClosed:true,legacyAndMalformedRecordsFailClosed:true,noInventedValuesOrEarlierHistory:true,noFailedPublication:true,editInvalidation:true,NativeUnchanged:true,browserObserved:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
