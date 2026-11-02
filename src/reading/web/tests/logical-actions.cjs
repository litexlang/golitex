'use strict';
// Actual native logical roles through the public reader's source events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node logical-actions.cjs <logic-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'logic-'+name+'.json'),'utf8'));
function records(bundle){
 const nodes=new Map(bundle.evidence_nodes.map(row=>[row.id,row.node]));
 const resolve=value=>{const seen=new Set();while(value?.kind==='evidence_reference'&&!seen.has(value.evidence_id)){seen.add(value.evidence_id);value=nodes.get(value.evidence_id);}return value||{};};
 const result=value=>{let node=resolve(value);while(node.fields?.['0'])node=resolve(node.fields['0']);return node;};
 return {nodes,resolve,result,success(type){return [...nodes.values()].find(node=>node.type===type);}};
}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let now=0,serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn,ms){timers.set(++serial,{fn,at:now+ms});return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const view={...dom,root,reader,row(line){const row=root.querySelector('[data-line="'+line+'"]');assert(row,line);return row;},
  async move(target){assert(target);if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');},
  async tick(ms){const end=now+ms;for(;;){const due=[...timers].filter(([,value])=>value.at<=end).sort((a,b)=>a[1].at-b[1].at)[0];if(!due)break;now=due[1].at;timers.delete(due[0]);await due[1].fn();await Promise.resolve();}now=end;},
  async hover(line,focus=false){const row=view.row(line);if(focus)await row.querySelector('.lr-line-number').trigger('focus');else await view.move(row.querySelector('.lr-source-code'));await view.tick(460);const card=root.querySelector('.lr-proof-popover');assert(card,'source card at '+line);return card;},
  async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'display views do not mutate native sources, facts, proofs or scope records');reader.destroy();}};
 return view;
}
const action=(view,line,kind)=>view.row(line).querySelector('[data-logical-kind="'+kind+'"]');
function sourceLine(bundle,text){const index=bundle.sources[0].content.split('\n').findIndex(line=>line.trim()===text);assert(index>=0,text);return index+1;}
async function run(){
 let checks=0;
 for(const locale of ['zh','en'])for(const editable of [true,false]){
  const bundle=fixture('sqrt-two'),data=records(bundle),statement=bundle.statements.find(s=>s.statement_kind?.endsWith('ByContraStmt')),success=data.success('ExecByContraStmtSuccess'),assumption=success.fields.reverse_assumption_fact_id.fact_id,goal=statement.mathematics.subject_fact_id,view=mount(bundle,locale,editable),head=statement.line,question=sourceLine(bundle,'? not sqrt(2) $in Q'),end=sourceLine(bundle,'impossible 2 <= gcd(p, q) = 1');
  assert(action(view,head,'conclusion').textContent.includes('∉'),'only the actual proved target appears at the header');
  assert.deepEqual(JSON.parse(view.row(head).dataset.proofFacts),[goal]);assert.deepEqual(JSON.parse(view.row(question).dataset.proofFacts),[assumption],'the question row owns only the native reverse assumption');
  assert(!action(view,question,'contra-assumption').textContent.includes('not'),'the negative target uses the retained positive assumption');
  let card=await view.hover(question);assert(card.textContent.includes(locale==='zh'?'目标的否定':'negation of the goal'));assert.equal(card.querySelector('.lr-proof-evidence .lr-fact-link').dataset.fact,assumption);
  const proof=card.querySelector('.lr-proof-evidence'),symbol=view.row(question).querySelectorAll('[data-symbol]').find(token=>token.textContent==='Q');assert(symbol);await view.move(symbol);assert.strictEqual(card,view.root.querySelector('.lr-proof-popover'));assert.strictEqual(proof,card.querySelector('.lr-proof-evidence'));assert(!card.querySelector('.lr-proof-symbol').hidden);
  assert(view.row(7).classList.contains('lr-context-active'),'the actual local proof scope is indicated');
  await view.close();assert(!view.row(7).classList.contains('lr-context-active'));
  card=await view.hover(end,true);assert(action(view,end,'contradiction'));assert.equal(card.querySelectorAll('.lr-proof-evidence .lr-proof-step').length,2);await view.row(end).querySelector('.lr-line-number').trigger('keydown',{key:'ArrowRight'});assert.strictEqual(view.document.activeElement,card.querySelector('.lr-proof-pin'),'keyboard access reaches a logical action without a stored source fact');
  for(const step of card.querySelectorAll('.lr-proof-evidence .lr-proof-step')){await step.querySelector('summary').click();assert(!step.textContent.includes('cannot be matched exactly'),step.textContent);}
  assert(card.textContent.includes(locale==='zh'?'分别验证每个相邻关系':'Verify each adjacent relation'),'a compound contradiction retains its individual chain proofs');
  await view.close();card=await view.hover(head);assert(card.textContent.includes(locale==='zh'?'解除反证假设':'discharges the temporary assumption'));const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);
  await view.close();card=await view.hover(sourceLine(bundle,'p / 2 $in Z'));assert(card.querySelectorAll('.lr-proof-grounds .lr-fact-link').some(link=>link.textContent.includes('2 ∣ p')),'the dividend/divisor order is preserved in mathematical divisibility notation');
  await view.close();card=await view.hover(head);
  await card.querySelector('.lr-proof-pin').click();assert.equal(view.reader.getSelection().fact,goal);assert.equal(view.reader.getSelection().focusLine,head,'the exported result navigates to its producing header');
  await view.root.trigger('keydown',{key:'Escape'});await action(view,question,'contra-assumption').click();assert.equal(view.reader.getSelection().focusLine,question);assert(view.root.querySelector('.lr-detail-body').textContent.includes(locale==='zh'?'目标的否定':'negation of the goal'));
  if(editable){const input=view.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(view.root.querySelectorAll('.lr-logical-action,.lr-inference-toggle,.lr-proof-popover,.lr-context-active').length,0,'editing invalidates logical actions and old conclusions');}
  view.done();checks++;
 }
 for(const locale of ['zh','en']){
  const bundle=fixture('contra-positive'),view=mount(bundle,locale),question=sourceLine(bundle,'? 0 $in {0}');assert(action(view,question,'contra-assumption').textContent.includes('∉'),'a positive goal uses its actual negative assumption');view.done();
  const cases=fixture('cases-scoped'),data=records(cases),statement=cases.statements.find(s=>s.statement_kind?.endsWith('ByCasesStmt')),success=data.success('ExecByCasesStmtSuccess'),branches=success.fields.branches.map(data.resolve),view2=mount(cases,locale),head=statement.line;
  assert(action(view2,head,'conclusion'));assert(action(view2,head+1,'case-goal'));assert(!view2.row(head+1).dataset.proofFacts,'the common goal is not a branch hypothesis or independent stored result');
  let card=await view2.hover(head);assert(card.querySelector('.lr-cases-proof'));assert(card.textContent.includes(locale==='zh'?'不要求各情况互斥':'need not be disjoint'));
  const coverage=card.querySelector('.lr-cases-proof .lr-proof-step');await coverage.querySelector('summary').click();assert(coverage.querySelector('.lr-fact-link'),'coverage follows the actual disjunction premise');
  const disclosures=card.querySelectorAll('.lr-case-proof');assert.equal(disclosures.length,2);for(const disclosure of disclosures){await disclosure.querySelector('summary').click();assert(disclosure.querySelector('.lr-proof-step'));}
  await view2.close();
  for(const [index,branch] of branches.entries()){
   const line=index===0?8:10,id=branch.fields.assumption_fact_id.fact_id,scope=data.resolve(branch.fields.local_env).scope_id,bodyLine=line+1;
   assert(action(view2,line,'case-assumption'));assert.deepEqual(JSON.parse(view2.row(line).dataset.proofFacts),[id]);
   card=await view2.hover(line);assert(card.textContent.includes(locale==='zh'?'仅在本分支内':'only within this case'));assert(view2.row(bodyLine).classList.contains('lr-context-active'));assert(!view2.row(index===0?11:9).classList.contains('lr-context-active'));
   await card.querySelector('.lr-proof-pin').click();assert.equal(view2.reader.getSelection().statement,statement.id);assert.equal(view2.reader.getSelection().focusLine,line);await view2.root.trigger('keydown',{key:'Escape'});
   card=await view2.hover(bodyLine);const context=card.querySelector('[data-scope="'+scope+'"]');assert(context,JSON.stringify({bodyLine,scope,content:card.textContent,contexts:card.querySelectorAll('.lr-proof-context').map(node=>node.dataset.scope)}));assert.deepEqual(context.querySelectorAll('.lr-fact-link').map(n=>n.dataset.fact),[id],'the local context links exactly this branch, never its sibling');await view2.close();
  }
  card=await view2.hover(1);assert(card.querySelector('.lr-claim-proof'));assert(card.querySelector('.lr-local-parameters').textContent.includes('x ∈ R'));assert(card.querySelector('.lr-proof-grounds .lr-fact-link'));
  await view2.close();card=await view2.hover(2);assert(card.textContent.includes(locale==='zh'?'任取声明范围内':'arbitrary parameters'));view2.done();checks++;
  const forall=fixture('forall'),fv=mount(forall,locale),statement2=forall.statements.find(s=>s.mathematics?.subject?.startsWith('forall'));
  card=await fv.hover(statement2.line);assert(card.querySelector('.lr-universal-proof'));assert(card.textContent.includes(locale==='zh'?'非空集合':'nonempty set'));assert(card.querySelector('.lr-proof-grounds .lr-fact-link'));fv.done();
 }
 for(const name of ['cases-missing','cases-false','contra-false']){
  const bundle=fixture(name),view=mount(bundle,'en');assert.equal(bundle.run_result,'failure');assert.equal(view.root.querySelectorAll('[data-logical-kind="conclusion"]').length,0,'these rejected targets have no completed outer conclusion');
  const data=records(bundle),retained=[...data.nodes.values()].filter(node=>['ByCasesBranchFailure','ByCasesBranchSuccess'].includes(node.type)).map(node=>({id:node.fields.assumption_fact_id.fact_id,line:data.result(node.fields.assumption).fields.line_file.line}));
  const assumptions=view.root.querySelectorAll('[data-logical-kind="case-assumption"]');assert.equal(assumptions.length,retained.length,'only actual retained case frames may introduce conditional assumptions');
  for(const note of assumptions){const line=Number(note.closest('.lr-code-row').dataset.line),expected=retained.filter(frame=>frame.line===line);assert(expected.length);await note.click();const ids=view.root.querySelectorAll('.lr-detail-body .lr-fact-link').map(link=>link.dataset.fact);assert(expected.every(frame=>ids.includes(frame.id)),'the source action shows its actual native case assumption');await view.close();}
  const line=Number(view.root.querySelector('.lr-rejected').dataset.line),card=await view.hover(line);assert(card.querySelector('.lr-failure-summary'));assert(!card.querySelector('.lr-cases-proof'));view.done();
 }
 for(const control of ['missing-store','missing-assumption','wrong-scope','wrong-source','outside-owner','wrong-command','wrong-identity','wrong-kind','legacy']){
  const bundle=fixture('sqrt-two'),data=records(bundle),success=data.success('ExecByContraStmtSuccess'),statement=bundle.statements.find(s=>s.statement_kind?.endsWith('ByContraStmt')),head=statement.line,question=sourceLine(bundle,'? not sqrt(2) $in Q');
  if(control==='missing-store')delete success.fields.stored;
  if(control==='missing-assumption')delete success.fields.reverse_assumption_fact_id;
  if(control==='wrong-scope')success.fields.local_env={kind:'scope',scope_id:'file:source0'};
  if(control==='wrong-source'||control==='outside-owner'){let node=data.result(success.fields.reverse_assumption);node.fields.line_file=control==='wrong-source'?{source_id:'absent',line:question}:{source_id:statement.source_id,line:1};}
  if(control==='wrong-command')data.result(success.fields.reverse_assumption).fields.line_file.line=sourceLine(bundle,'impossible 2 <= gcd(p, q) = 1');
  if(control==='wrong-identity')success.fields.reverse_assumption_fact_id={kind:'fact_reference',fact_id:statement.mathematics.subject_fact_id};
  if(control==='wrong-kind')statement.statement_kind='By.FutureProofStmt';
  if(control==='legacy')for(const key of ['stored','goal','reverse_assumption','reverse_assumption_fact_id','assumption_components','negation_assumed','local_env'])delete success.fields[key];
  const view=mount(bundle,'en');if(['missing-store','legacy'].includes(control))assert(!action(view,head,'conclusion'));if(control!=='missing-store')assert(!action(view,question,'contra-assumption'));view.done();
 }
 for(const locale of ['zh','en']){
  const bundle=fixture('contra-classified'),view=mount(bundle,locale),lines=bundle.sources[0].content.split('\n');
  assert(view.root.querySelectorAll('[data-logical-kind="contra-assumption"]').length>=6);
  assert(view.root.querySelectorAll('[data-logical-kind="case-assumption"]').length>=4);
  for(const note of view.root.querySelectorAll('[data-logical-kind="case-assumption"]'))assert(lines[Number(note.closest('.lr-code-row').dataset.line)-1].trim().startsWith('case '));
  for(const toggle of view.root.querySelectorAll('.lr-inference-toggle'))assert.equal(toggle.textContent,(locale==='zh'?'推论 ':'Consequences ')+JSON.parse(toggle.dataset.facts).length+' ▸','inference results remain collapsed');
  const counts=view.root.querySelectorAll('.lr-code-row').length;assert.equal(counts,lines.length,'logical notes add no source rows');view.done();
 }
 for(const locale of ['zh','en']){
  const bundle=fixture('contra-compound'),view=mount(bundle,locale),endings=view.root.querySelectorAll('[data-logical-kind="contradiction"]').map(note=>Number(note.closest('.lr-code-row').dataset.line));assert.equal(endings.length,3);
  for(const line of endings){const card=await view.hover(line),proof=card.querySelector('.lr-proof-evidence');assert.equal(proof.querySelectorAll('.lr-proof-step').length,2,'both actual proofs of a compound contradiction are readable');for(const step of proof.querySelectorAll('.lr-proof-step')){await step.querySelector('summary').click();assert(!step.textContent.includes('cannot be matched exactly'));}await view.close();}view.done();
  const claim=fixture('claim'),cv=mount(claim,locale);for(const statement of claim.statements.filter(s=>s.statement_kind?.endsWith('ClaimStmt'))){const card=await cv.hover(statement.line),proof=card.querySelector('.lr-claim-proof');assert(proof);const closing=proof.querySelector('.lr-proof-step');assert(closing);await closing.querySelector('summary').click();assert(!closing.textContent.includes('cannot be matched exactly'));await cv.close();}cv.done();
  const cantor=fixture('cantor'),data=records(cantor),av=mount(cantor,locale),statement=cantor.statements.find(s=>s.statement_kind?.endsWith('ByContraStmt')),record=data.result(statement.evidence),question=statement.line+1,scope=data.resolve(record.fields.local_env).scope_id,toggle=av.row(question).querySelector('.lr-inference-toggle');assert(toggle,'the native temporary surjectivity assumption has actual inferences');
  const reachable=new Set();function visit(value){if(value?.kind==='evidence_reference'){if(reachable.has(value.evidence_id))return;reachable.add(value.evidence_id);visit(data.resolve(value));}else if(value&&typeof value==='object')for(const child of Object.values(value))visit(child);}
  visit(data.resolve(record.fields.negation_assumed).fields.infer);const expected=[...new Set(cantor.inferences.filter(batch=>reachable.has(batch.evidence?.evidence_id)).flatMap(batch=>batch.fact_ids))].sort();assert.deepEqual(JSON.parse(toggle.dataset.facts).sort(),expected,'the question row lists only this assumption store’s actual infer outputs');
  const headerToggle=av.row(statement.line).querySelector('.lr-inference-toggle');assert(!headerToggle||JSON.parse(headerToggle.dataset.facts).every(id=>!expected.includes(id)),'temporary inferences do not become outer conclusions');
  await toggle.click();const panel=av.root.querySelector('.lr-inference-popover'),disclosure=panel.querySelector('details');assert(!disclosure.open);await disclosure.querySelector('summary').click();const result=disclosure.querySelector('.lr-inferred-result');assert(result);await result.click();assert.equal(av.reader.getSelection().focusLine,question,'a local inference navigates to its actual assumption anchor');assert(av.root.querySelector('.lr-detail-body [data-scope="'+scope+'"]'),'the derived fact retains its temporary assumption context');await av.root.querySelector('.lr-back').click();assert.equal(av.reader.getSelection().focusLine,question);av.done();
  const repeated=fixture('repeated'),rv=mount(repeated,locale),instances=repeated.statements.filter(s=>s.source_statement_id==='statement1');assert.equal(instances.length,2);assert.notEqual(instances[0].scope_id,instances[1].scope_id);
  await rv.row(instances[0].line).querySelector('.lr-line-number').click();let choices=rv.root.querySelectorAll('.lr-contexts .lr-chip');assert.equal(choices.length,2,'repeated source execution choices remain accessible from the line');
  for(const [index,instance] of instances.entries()){
   choices=rv.root.querySelectorAll('.lr-contexts .lr-chip');await choices[index].click();assert.equal(rv.reader.getSelection().statement,instance.id);const id=instance.mathematics.subject_fact_id,producer=repeated.facts.find(f=>f.id===id).producer_statement_id;assert.deepEqual(JSON.parse(rv.row(instance.line).dataset.proofFacts||'[]'),producer===instance.id?[id]:[],'a reused native FactId is not promoted into a new scope or assigned a new producer');
   await rv.close();const card=await rv.hover(instance.line);assert.equal(card.querySelector('.lr-logical-proof').dataset.statement,instance.id);assert(card.querySelector('[data-scope="'+instance.scope_id+'"]'),'each repeated source step uses its own execution scope');await rv.close();await rv.row(instance.line).querySelector('.lr-line-number').click();
  }rv.done();
 }
 for(const control of ['missing-groups','unknown-kind']){
  const bundle=fixture('cases-scoped'),data=records(bundle),claim=data.success('ExecClaimStmtSuccess'),goal=data.resolve(data.resolve(claim.fields.statement).fields.fact),universal=data.resolve(goal.fields['0']),parameters=data.resolve(universal.fields.typed_parameters);
  if(control==='missing-groups')delete parameters.fields.groups;else data.resolve(data.resolve(parameters.fields.groups[0]).fields.param_type).variant='UnknownDomain';
  const view=mount(bundle,'en'),card=await view.hover(2),local=card.querySelector('.lr-local-parameters');assert(local.textContent.includes('not fully exported'));assert.equal(local.querySelectorAll('.lr-formula').length,0,'missing domains are not reconstructed from source spelling');view.done();
 }
 console.log(JSON.stringify({passed:true,bilingualEditableAndReadOnly:checks,actualNegationAndSourceAnchors:true,contradictionClosures:true,compoundExistentialAndUniversalClosures:true,caseCoverageAndExactLocalScopes:true,claimAndUniversalContext:true,actualLocalInferences:true,repeatedExecutionChoicesNotMerged:true,factAndSymbolCompartments:true,pinAndEditInvalidation:true,rejectedAndMissingRecordsNotGuessed:true,collapsedConsequencesAndNoExtraRows:true,nativeRecordsUnchanged:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
