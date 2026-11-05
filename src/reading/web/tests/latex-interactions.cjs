'use strict';
// Source/math differential acceptance through the public reader and actual CLI.
// No fixture archives, browser layout simulation, TeX parsing or proof replay.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict'),{spawnSync}=require('node:child_process');
const {createDOM}=require('./dom.cjs'),katex=require('../vendor/katex/katex.min.js');
const binary=path.resolve(process.argv[2]||'target/release/litex'),code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
function native(file,expected=0){
 const content=fs.readFileSync(file,'utf8'),run=spawnSync(binary,['-reading','-latex','-strict','-json','-lang','en','-e',content],{encoding:'utf8',maxBuffer:64*1024*1024});
 assert(!run.error,run.error?.message);assert(expected===null?[0,1].includes(run.status):run.status===expected,run.stderr||file);
 const data=JSON.parse(run.stdout);assert.equal(data.sources[0].content,content);assert.equal(data.run_result,run.status===0?'success':'failure');return data;
}
function mount(data,locale='en',editable=false,layout='latex'){
 const before=JSON.stringify(data),dom=createDOM(),root=dom.root(),timers=new Map();let now=0,serial=0;
 dom.window.katex={render(tex,node,options){katex.renderToString(tex,options);node.textContent=tex;}};
 vm.runInContext(code,vm.createContext({...dom,URL,TextEncoder,Map,Set,console,setTimeout(fn,delay){timers.set(++serial,{fn,at:now+delay});return serial;},clearTimeout:id=>timers.delete(id)}));
 const reader=dom.window.LitexReading.mount(root,{document:data,locale,layout,...(editable?{onCheck:async()=>data}:{})});
 return {...dom,root,reader,card(){return root.querySelector('.lr-proof-popover');},unit(statement){return root.querySelectorAll('[data-latex-statement]').find(node=>node.dataset.latexStatement===(statement.source_statement_id||statement.id));},
  async tick(ms){const end=now+ms;for(;;){const due=[...timers].filter(([,t])=>t.at<=end).sort((a,b)=>a[1].at-b[1].at)[0];if(!due)break;now=due[1].at;timers.delete(due[0]);await due[1].fn();}now=end;},
  async hover(unit){await unit.trigger('pointerenter');await this.tick(460);return this.card();},
  done(){assert.equal(JSON.stringify(data),before,'all Native proof, symbol, source and scope records remain unchanged');reader.destroy();}
 };
}
function proofText(card){return card.querySelector('.lr-proof-evidence').children.filter(node=>!node.classList.contains('lr-math-reading-tools')&&!node.classList.contains('lr-math-source')).map(node=>node.textContent).join('');}
async function main(){
 const newton=native('examples/reading/homepage/03-newton-error.lit'),flow=native('examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit'),failed=native('examples/reading/lessons/en/sqrt-domain.lit',1),repeated=native('examples/test_statements/by_enumerate_finite_set_stmt.lit',null);
 let mirrors=0,interactions=0;
 for(const locale of ['en','zh'])for(const editable of [false,true]){
  const view=mount(newton,locale,editable),chain=newton.statements.find(s=>s.line===9&&s.statement_kind==='Fact'),unit=view.unit(chain),initial=JSON.stringify(view.reader.getSelection());
  let card=await view.hover(unit);assert(card.querySelector('.lr-proof-evidence'));assert(card.querySelector('.lr-proof-context'),'arbitrary parameters and local premises are visible');
  assert.equal(JSON.stringify(view.reader.getSelection()),initial,'hover never navigates');assert(!card.querySelector('.lr-math-source').open);assert.equal(card.querySelector('.lr-formal-source pre').textContent,Buffer.from(newton.sources[0].content).subarray(chain.start_byte,chain.end_byte).toString().trimEnd());
  const tools=card.querySelector('.lr-math-reading-tools'),stepList=tools.querySelector('.lr-math-steps');assert(stepList);assert.equal(stepList.querySelectorAll('.lr-math-equality-step').length,2,'two retained adjacent equalities');
  const symbols=tools.querySelector('.lr-math-symbols');assert(symbols);await symbols.querySelector('summary').click();
  const functionSymbol=newton.symbols.find(s=>s.name==='newton'),token=symbols.querySelectorAll('.lr-math-symbol').find(n=>n.dataset.symbol===functionSymbol.id);assert(token);
  const evidence=card.querySelector('.lr-proof-evidence'),oldProof=proofText(card);evidence.scrollTop=38;await unit.click();assert.strictEqual(view.card(),card,'pinning preserves the complete proof DOM');
  await token.click();assert.strictEqual(view.card(),card);const info=card.querySelector('.lr-proof-symbol');assert(!info.hidden);assert(info.querySelector('.lr-definition-source').textContent.includes('have fn newton'));assert(info.querySelector('.lr-math-definition'),'the exact compiler definition is shown as mathematics');assert.equal(info.querySelector('.lr-math-definition').lang,newton.language,'definition prose retains its compiler language across UI locale changes');assert(!info.querySelector('.lr-math-definition button'),'definition mathematics has no inert proof controls');assert(!info.querySelector('.lr-math-definition-source').open,'formal definition source is initially folded');assert.equal(proofText(card),oldProof);assert.equal(evidence.scrollTop,38);
  const rToken=symbols.querySelectorAll('.lr-math-symbol').find(n=>n.dataset.symbol&&n.textContent==='r');await rToken.trigger('mouseenter');assert.strictEqual(view.card(),card);assert(card.querySelector('.lr-proof-symbol').textContent.includes('sqrt'));assert.equal(evidence.scrollTop,38);assert(symbols.open,'symbol changes preserve disclosure state');
  await unit.click();assert(!view.card(),'a second click closes the pinned preview');await view.tick(1000);assert(!view.card());
  card=await view.hover(unit);await unit.click();await card.querySelector('.lr-math-steps summary').click();
  const step=card.querySelectorAll('.lr-math-equality-step')[1],chainId=chain.mathematics.subject_fact_id;await step.click();assert.equal(view.reader.getSelection().fact,chainId);assert.equal(view.reader.getSelection().chainStep,1);assert(view.root.querySelector('.lr-context-explanation'));assert(view.root.querySelector('.lr-manuscript'));
  const selectedStep=JSON.stringify(view.reader.getSelection()),citation=view.root.querySelector('.lr-detail-body .lr-fact-link');assert(citation);const cited=citation.dataset.fact;await citation.click();assert.equal(view.reader.getSelection().fact,cited);await view.root.querySelector('.lr-back').click();assert.equal(JSON.stringify(view.reader.getSelection()),selectedStep,'citation Back restores the exact equality index');
  const back=view.root.querySelector('.lr-back');assert(back);await back.click();assert.equal(view.reader.getSelection().fact,chainId);assert.equal(view.reader.getSelection().chainStep,null,'Back restores the whole chain address');await view.root.trigger('keydown',{key:'Escape'});
  const currentUnit=view.unit(chain),piece=view.root.querySelectorAll('[data-latex-statement]').find(n=>n!==currentUnit&&n.dataset.latexStatement===chain.id);
  await currentUnit.trigger('pointerenter');await view.tick(220);await currentUnit.trigger('pointerleave');await piece.trigger('pointerenter');await view.tick(240);assert(view.card(),'moving across one compiler statement preserves its initial dwell');const stable=view.card();await piece.trigger('pointerleave');await currentUnit.trigger('pointerenter');await view.tick(500);assert.strictEqual(view.card(),stable,'same-statement fragments retain expanded evidence');
  await view.root.trigger('keydown',{key:'Escape'});
  const result=view.root.querySelectorAll('.lr-math-consequences').find(n=>n.closest('.lr-math-context').dataset.statement===chain.id);assert(result,'actual inferred consequences are available beside the formula');const ids=JSON.parse(result.dataset.facts);assert(ids.every(id=>chain.inferred_fact_ids.includes(id)));
  await result.click();const panel=view.root.querySelector('.lr-inference-popover');assert(panel);await panel.querySelector('summary').click();const actual=panel.querySelector('.lr-inferred-result'),id=actual.dataset.fact;await actual.click();assert.equal(view.reader.getSelection().fact,id);await view.root.querySelector('.lr-back').click();assert.equal(view.reader.getSelection().statement,chain.id,'inference Back retains its producing execution');await view.root.trigger('keydown',{key:'Escape'});
  await view.root.querySelector('[data-layout="source"]').click();if(editable){const input=view.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!view.root.querySelector('.lr-math-reason,.lr-math-consequences,.lr-proof-popover'));assert(view.root.querySelector('[data-layout="latex"]').disabled);}else{await view.root.querySelector('[data-layout="latex"]').click();assert(view.root.querySelector('.lr-manuscript'));}
  view.done();interactions++;
 }
 // Compare complete source evidence, rather than asserting a hand-authored
 // narrative for each kernel branch or selecting a route by formula text.
 for(const data of [newton,flow,failed,repeated])for(const locale of ['en','zh']){
  const source=mount(data,locale,false,'source'),math=mount(data,locale);
  for(const statement of data.statements.filter(s=>(s.source_statement_id||s.id)===s.id)){
   const row=source.root.querySelectorAll('.lr-code-row').find(r=>r.dataset.statement===statement.id&&Number(r.dataset.line)===statement.line),unit=math.unit(statement);if(!row||!unit)continue;
   await row.trigger('pointermove',{target:row.querySelector('.lr-source-code')});await source.tick(460);const original=source.card();if(!original)continue;
   const card=await math.hover(unit);assert(card);assert.equal(proofText(card),proofText(original),statement.statement_kind+' line '+statement.line+' must use the full current source proof/action/failure renderer');
   const condition=card.querySelector('.lr-atomic-wd');if(condition)assert(!condition.open);assert(!card.querySelector('.lr-math-source').open);
   await source.root.trigger('keydown',{key:'Escape'});await math.root.trigger('keydown',{key:'Escape'});mirrors++;
  }
  source.done();math.done();
 }
 const groups=new Map();for(const statement of repeated.statements){const id=statement.source_statement_id||statement.id;if(!groups.has(id))groups.set(id,[]);groups.get(id).push(statement);}
 const executions=[...groups.values()].find(items=>items.length>1&&items[0].statement_kind==='Fact'),original=executions.find(s=>(s.source_statement_id||s.id)===s.id),repeat=mount(repeated);
 let contextCard=await repeat.hover(repeat.unit(original));assert.equal(contextCard.querySelectorAll('.lr-math-executions .lr-chip').length,executions.length);
 for(const execution of executions.filter(s=>s.status==='accepted')){
  const pick=contextCard.querySelectorAll('.lr-math-executions .lr-chip').find(n=>n.dataset.statement===execution.id);await pick.click();assert.equal(repeat.reader.getSelection().statement,execution.id);await repeat.root.trigger('keydown',{key:'Escape'});
  const unit=repeat.unit(original);assert.equal(unit.dataset.statement,execution.id);contextCard=await repeat.hover(unit);const proof=contextCard.querySelector('.lr-logical-proof');assert(proof);assert.equal(proof.dataset.statement,execution.id,'the selected execution supplies its own checked proof, not another instance');
  assert.equal(contextCard.querySelector('.lr-math-executions [aria-pressed="true"]').dataset.statement,execution.id);
 }repeat.done();
 // Pointer exit before dwell, keyboard entry, rejection, and honest missing data.
 const view=mount(failed),statement=failed.statements.find(s=>s.status==='rejected'),unit=view.unit(statement);assert(unit.classList.contains('lr-latex-rejected'));
 await unit.trigger('pointerenter');await view.tick(200);await unit.trigger('pointerleave');await view.tick(500);assert(!view.card(),'leaving before dwell cannot open a stale explanation');
 await unit.trigger('focus');await view.tick(460);const formation=view.card().querySelector('.lr-atomic-wd');if(formation)await formation.querySelector('summary').click();assert(view.card().textContent.includes('0'),view.card().textContent);assert(!view.card().querySelector('.lr-math-steps'));await view.root.trigger('keydown',{key:'Escape'});view.done();
 for(const corruption of ['occurrence','source','steps']){
  const data=structuredClone(newton),chain=data.statements.find(s=>s.line===9&&s.statement_kind==='Fact');
  if(corruption==='occurrence')data.occurrences=data.occurrences.map(o=>({...o,symbol_id:'missing'}));
  if(corruption==='source')data.occurrences=data.occurrences.map(o=>({...o,source_id:'foreign'}));
  if(corruption==='steps')delete data.facts.find(f=>f.id===chain.mathematics.subject_fact_id).evidence;
  const v=mount(data),card=await v.hover(v.unit(chain));assert(card);
  if(corruption==='steps')assert(!card.querySelector('.lr-math-steps'),'missing adjacent certificates do not manufacture step controls');
  else assert(!card.querySelector('.lr-math-symbol[data-symbol]'),'foreign/missing symbol identity cannot borrow a definition');v.done();
 }
 const missingDefinition=structuredClone(newton),definition=missingDefinition.statements.find(s=>s.statement_kind==='Definition.HaveFnEqualStmt'),source=missingDefinition.sources.find(s=>s.id===definition.source_id);source.latex_blocks=source.latex_blocks.filter(block=>block.start_byte!==definition.start_byte);
 const fallback=mount(missingDefinition),goal=missingDefinition.statements.find(s=>s.line===9&&s.statement_kind==='Fact'),fallbackCard=await fallback.hover(fallback.unit(goal));await fallbackCard.querySelector('.lr-math-symbols summary').click();const name=missingDefinition.symbols.find(s=>s.name==='newton');await fallbackCard.querySelectorAll('.lr-math-symbol').find(n=>n.dataset.symbol===name.id).click();assert(!fallbackCard.querySelector('.lr-math-definition'),'a missing definition block cannot borrow the enclosing proof or a neighboring formula');assert(fallbackCard.querySelector('.lr-definition-source').textContent.includes('have fn newton'));fallback.done();
 const registeredRun=spawnSync(binary,['-reading','-latex','-strict','-json','-lang','en','-f','examples/reading/homepage/03-newton-error.lit'],{encoding:'utf8',maxBuffer:64*1024*1024});assert.equal(registeredRun.status,0,registeredRun.stderr);const registered=JSON.parse(registeredRun.stdout),chapter=registered.sources.find(s=>s.path.endsWith('03-newton-error.lit')),chain=registered.statements.find(s=>s.source_id===chapter.id&&s.line===9&&s.statement_kind==='Fact');
 assert(chapter.latex_blocks.some(block=>block.content.includes('::')),'the registered compiler retains its actual qualified names');
 for(const missingConfig of [false,true]){
  const data=structuredClone(registered);if(missingConfig)for(const entry of data.configurations)delete entry.configuration.exports;
  const v=mount(data),math=v.root.querySelectorAll('[data-latex-statement]').find(n=>n.dataset.latexStatement===chain.id&&n.getAttribute('aria-label')?.includes('newton'));assert(math);
  assert.equal(math.getAttribute('aria-label').includes('::'),missingConfig,'only the existing resolved display-name correspondence may shorten compiler identifiers');v.done();
 }
 assert(mirrors>20);console.log(JSON.stringify({passed:true,fullSourceProofMirrors:mirrors,bilingualEditableInteractions:interactions,exactNativeAdjacentSteps:true,independentSymbolsAndProof:true,nativeConsequencesAndBack:true,statementDwellAndKeyboard:true,conditionalRepeatedAndFailedRoutes:true,missingAndForeignEvidence:true,resolvedDisplayNamesWithMissingMetadataControl:true,nativeUnchanged:true,browserGeometry:false}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
