'use strict';
// Actual checked clauses, including closing checks without a stored Fact row.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node local-source-equalities.cjs <native-fixtures> [actual-export]');
const code=fs.readFileSync(process.env.LITEX_READER_JS||path.join(__dirname,'../reader.js'),'utf8');
function fixture(name){const standard=path.join(directory,'local-equality-'+name+'.json');return JSON.parse(fs.readFileSync(fs.existsSync(standard)?standard:path.join(directory,name+'.json'),'utf8'));}
function records(b){const nodes=new Map(b.evidence_nodes.map(row=>[row.id,row.node]));function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}function result(v){let n=resolve(v);const seen=new Set();while(n.fields?.['0']&&!seen.has(n)){seen.add(n);n=resolve(n.fields['0']);}return n;}return {nodes,resolve,result};}
function mount(bundle,locale,editable=true,readerCode=code){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(readerCode,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const view={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,line);return row;},async flush(){for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}},async hover(target,keyboard=false){if(keyboard){target.focus();await view.flush();}else{if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');await view.flush();}const card=root.querySelector('.lr-proof-popover');assert(card,'actual source hover');return card;},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'source, Native facts, IDs, evidence and scopes are immutable');assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length);reader.destroy();}};
 return view;
}
function checked(b,line){const d=records(b);for(const s of b.statements){const goal=[...d.nodes.values()].find(n=>n.type==='ForallFact'&&n.fields.fact_id.fact_id===s.mathematics?.subject_fact_id);for(const value of goal?.fields.then_facts||[]){const subject=d.result(value);if(subject.fields?.line_file?.line!==line)continue;const proof=[...d.nodes.values()].find(n=>['VerifyChainFactSuccess','VerifyEqualitySuccess'].includes(n.type)&&d.result(n.fields.fact)===subject);if(proof)return {d,proof,subject};}}throw new Error('actual checked source clause at line '+line);}
function wdLast(card){const wd=card.querySelector('.lr-atomic-wd');assert(wd&&!wd.open,'own WD is closed');assert.equal(wd.parentNode.children.at(-1),wd,'own WD is final');}
const positives=[['failed-prefix',4,[0,1]],['successful-universal',2,[0,1]],['claim-closing-prefix',5,[0,1]],['nested-claim',9,[0,1]],['atomic-local',4,[0]],['theorem',3,[0,1]],['strategy-with-body',3,[0,1]],['cited-equalities',5,[0,1]],['mixed-chain',4,[1]]];
async function exercise(bundle,locale,editable,line,indexes,readerCode=code){
 const v=mount(bundle,locale,editable,readerCode),{d,proof,subject}=checked(bundle,line),id=subject.fields.fact_id.fact_id,row=v.row(line),owner=row.dataset.statement,targets=row.querySelectorAll('.lr-chain-equality');
 assert.deepEqual(targets.map(n=>Number(n.dataset.chainStep)),indexes,'each retained adjacent equality is addressable at its source');
 for(const index of indexes){
  let token=v.row(line).querySelectorAll('.lr-chain-equality').find(n=>Number(n.dataset.chainStep)===index);assert.equal(token.dataset.chainFact,id,'retain the actual source-clause FactId');
  const card=await v.hover(token),proofBody=card.querySelector('.lr-proof-evidence'),adjacent=proof.type==='VerifyChainFactSuccess'?proof.fields.adjacent[index]:proof,relation=d.result(adjacent),left=d.resolve(d.resolve(relation.fields.fact).fields.left).text,right=d.resolve(d.resolve(relation.fields.fact).fields.right).text;
  assert.equal(proofBody.querySelector('.lr-formula').textContent,left+' = '+right,'only the selected endpoints');assert(!proofBody.querySelector('.lr-empty-note')?.textContent.includes('No separate proof'));wdLast(proofBody);assert(proofBody.querySelector('.lr-proof-context'),'the real local context accompanies the proof');
  if(bundle.sources[0].content.includes('first = middle')){const premise=bundle.facts.find(f=>f.line===index+2&&f.role==='hypothesis');assert(premise);assert.deepEqual(proofBody.querySelectorAll('.lr-fact-link').filter(n=>!n.closest('.lr-proof-context')).map(n=>n.dataset.fact),[premise.id],'each equals uses its own actual cited premise');assert(v.row(index+2).classList.contains('lr-proof-premise'));assert(!v.row(index===0?3:2).classList.contains('lr-proof-premise'),'the other equality premise is context, not this step\'s citation');}
  if(bundle.sources[0].content.includes('? forall a R:'))assert.equal(proofBody.querySelectorAll('.lr-proof-context').length,2,'retain both nested scopes');
  await v.hover(token);assert.strictEqual(v.root.querySelector('.lr-proof-popover'),card,'an unchanged equality target keeps its proof');
  await card.querySelector('.lr-proof-pin').click();let selection=v.reader.getSelection();assert.equal(selection.chainStep,index);assert.equal(selection.statement,owner);assert.equal(selection.focusLine,line);assert.equal(v.root.querySelector('.lr-detail-body .lr-formula').textContent,left+' = '+right);wdLast(v.root.querySelector('.lr-detail-body'));
  const scope=v.root.querySelector('.lr-detail-body .lr-proof-context .lr-math-link');assert(scope);await scope.click();await v.root.querySelector('.lr-back').click();selection=v.reader.getSelection();assert.equal(selection.chainStep,index);assert.equal(selection.focusLine,line);assert.equal(selection.issue,null);assert(!v.root.querySelector('.lr-context-explanation').hidden);assert.equal(v.root.querySelector('.lr-detail-body .lr-formula').textContent,left+' = '+right);
  const cite=v.root.querySelector('.lr-detail-body .lr-fact-link');if(cite){const citedId=cite.dataset.fact;await cite.click();assert.equal(v.reader.getSelection().fact,citedId);await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().chainStep,index);assert.equal(v.reader.getSelection().focusLine,line);assert.equal(v.root.querySelector('.lr-detail-body .lr-formula').textContent,left+' = '+right);}
  await v.close();token=v.row(line).querySelectorAll('.lr-chain-equality').find(n=>Number(n.dataset.chainStep)===index);await v.hover(token,true);await token.trigger('keydown',{key:'Enter'});assert.equal(v.reader.getSelection().chainStep,index);await v.close();
 }
 await v.row(line).querySelector('.lr-line-number').click();assert.equal(v.reader.getSelection().chainStep,null,'line selection restores whole-clause proof');assert(v.root.querySelector('.lr-detail-body .lr-atomic-wd'));await v.close();
 const rowPreview=await v.hover(v.row(line).querySelector('.lr-source-code')),symbol=v.row(line).querySelector('[data-symbol]');if(symbol){const body=rowPreview.querySelector('.lr-proof-evidence');await v.hover(symbol);assert.strictEqual(v.root.querySelector('.lr-proof-popover .lr-proof-evidence'),body,'symbol help does not replace the whole-clause proof');}await v.close();
 if(bundle.run_result==='failure'){assert(!v.root.querySelector('[data-logical-kind="conclusion"]'),'no outer publication');const failed=bundle.statements.find(s=>s.id===owner);if(failed.status==='rejected')assert.equal(failed.produced_fact_ids.length,0);}
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-chain-equality,.lr-proof-popover,.lr-logical-action').length,0);}
 v.done();
}
async function run(){let checkedCases=0;
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const[name,line,indexes]of positives){await exercise(fixture(name),locale,editable,line,indexes);checkedCases++;}
 for(const locale of ['zh','en'])for(const[name,line]of [['definition',2],['unexecuted-chain',5],['claim-before-closing',3]]){const b=fixture(name),v=mount(b,locale);assert.equal(v.row(line).querySelectorAll('.lr-chain-equality').length,0,'unchecked declarations do not get proof controls');v.done();checkedCases++;}
 for(const locale of ['zh','en']){const b=fixture('failed-chain'),v=mount(b,locale);assert.deepEqual(v.row(4).querySelectorAll('.lr-chain-equality').map(n=>[Number(n.dataset.chainStep),n.dataset.chainStatus]),[[0,'verified'],[1,'rejected']],'a partial chain distinguishes the actual checked and failed relations');assert(!v.row(4).querySelector('[data-logical-kind="local-conclusion"]'),'a failed chain is not a completed local conclusion');v.done();checkedCases++;}
 for(const control of ['missing-proof','wrong-endpoint','wrong-operator','wrong-goal','foreign-source','foreign-scope','foreign-owner','wrong-clause','ambiguous-primary']){
  const b=fixture('failed-prefix'),{d,proof,subject}=checked(b,4),s=b.statements[0],failure=[...d.nodes.values()].find(n=>n.type==='VerifyForallFactFailed'),goal=d.result(failure.fields.fact);
  if(control==='missing-proof')proof.fields.adjacent[0]={kind:'unavailable'};
  if(control==='wrong-endpoint')d.resolve(d.result(proof.fields.adjacent[0]).fields.fact).fields.left={kind:'unavailable'};
  if(control==='wrong-operator')subject.fields.prop_names[0]={kind:'symbol_reference',name:'<',symbol_id:'foreign'};
  if(control==='wrong-goal')s.mathematics.subject_fact_id='foreign';
  if(control==='foreign-source')subject.fields.line_file.source_id='foreign';
  if(control==='foreign-scope')failure.fields.local_env={kind:'scope',scope_id:'file:source0'};
  if(control==='foreign-owner')b.scopes.find(row=>row.id===d.resolve(failure.fields.local_env).scope_id).statement_id='foreign';
  if(control==='wrong-clause')goal.fields.then_facts[0]=goal.fields.then_facts[1];
  if(control==='ambiguous-primary'){const fact=b.facts.find(f=>f.id===subject.fields.fact_id.fact_id);b.facts.push({...fact,id:'conflicting-source-proof',producer_statement_id:null});}
  const v=mount(b,'en'),indexes=v.row(4).querySelectorAll('.lr-chain-equality').map(n=>Number(n.dataset.chainStep));assert.deepEqual(indexes,['missing-proof','wrong-endpoint'].includes(control)?[1]:[],control+' cannot borrow another proof or source');v.done();checkedCases++;
 }
 if(process.argv[3]){const exported=path.resolve(process.argv[3]),b=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),actual=fs.readFileSync(path.join(exported,'reader.js'),'utf8'),line=b.sources[0].content.split('\n').findIndex(row=>row.trim()==='x + 0 = x = 0 + x')+1;assert(line);for(const locale of ['zh','en'])await exercise(b,locale,false,line,[0,1],actual);checkedCases+=2;}
 console.log(JSON.stringify({passed:true,checked:checkedCases,bilingualEditableAndReadOnly:true,actualAdjacentProofsAndLocalScopes:true,closingChecksWithoutStoredFacts:true,hoverPinKeyboardAndExactBack:true,wholeClauseAndEditInvalidation:true,missingAndForeignNotGuessed:true,noOuterPublication:true,nativeRecordsUnchanged:true,actualExport:!!process.argv[3],browserObserved:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
