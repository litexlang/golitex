'use strict';
// Actual native function interfaces, retained call layers and public hover events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node function-properties.cjs <native-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
function records(bundle){const nodes=new Map(bundle.evidence_nodes.map(row=>[row.id,row.node]));function resolve(value){const seen=new Set();while(value?.kind==='evidence_reference'&&!seen.has(value.evidence_id)){seen.add(value.evidence_id);value=nodes.get(value.evidence_id);}return value||{};}function frames(value){const chain=[];let node=resolve(value);while(node&&node.type){chain.push(node);if(node.fields?.searched_proof)node=resolve(node.fields.searched_proof);else if(node.fields?.['0'])node=resolve(node.fields['0']);else break;}return chain;}return {nodes,resolve,frames};}
function mount(bundle,locale,editable){const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;vm.runInContext(code,vm.createContext({...dom,console,TextEncoder,URL,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});return {...dom,root,reader,async move(target){assert(target);if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},done(){assert.equal(JSON.stringify(bundle),before,'native source/proof/FactId/scope records are unchanged');reader.destroy();}};}
async function open(node){assert(node);if(!node.open)await node.querySelector('summary').click();}
const read=name=>JSON.parse(fs.readFileSync(path.join(directory,'function-property-'+name+'.json'),'utf8'));
const owners=['KnownFunctionInExactCarrierProof','DeclaredFunctionInExactCarrierProof','FnApplicationInStandardSupersetProof','FnApplicationInCodomainKnownSpecialPropertyProof'];
function lastFact(bundle){return bundle.facts.findLast(fact=>fact.producer_statement_id===bundle.statements.at(-1).id&&fact.is_primary&&fact.role==='verified');}
async function show(bundle,locale='en',editable=true){const view=mount(bundle,locale,editable),statement=bundle.statements.at(-1),row=view.root.querySelector('[data-line="'+statement.line+'"]'),card=await view.move(row.querySelector('.lr-source-code'));assert(card);return {view,row,card,part:card.querySelector('.lr-function-property-proof')};}
async function run(){let checked=0;const families=new Set(),views=[];
 for(const file of fs.readdirSync(directory).filter(file=>/^function-property-.*\.json$/.test(file)).sort())for(const locale of ['zh','en'])for(const editable of [true,false]){
  const bundle=JSON.parse(fs.readFileSync(path.join(directory,file),'utf8')),d=records(bundle),fact=lastFact(bundle),owner=fact&&d.frames(fact.evidence).find(node=>owners.includes(node.type)),{view,row,card,part}=await show(bundle,locale,editable);
  if(bundle.run_result==='failure'||!owner){assert(!part,'failure or another actual proof route keeps its own consumer: '+file);view.done();checked++;continue;}
  families.add(owner.type);assert(part,file+': proof route');
  const legacyAlias=file.includes('aliased-nested')&&!owner.fields.applied&&!d.resolve(owner.fields.signature_returns?.[0]).fields?.applied;
  assert.equal(part.dataset.status,legacyAlias?'incomplete':'retained',file+': '+part.textContent);
  if(legacyAlias){assert(!part.querySelector('.lr-function-call-binding'));view.done();checked++;continue;}
  assert(!/__param_\d+|f\d+::/.test(part.textContent),part.textContent);
  if(part.dataset.kind.endsWith('exact')){
   const interfaces=part.querySelector('.lr-function-exact-interfaces');assert(interfaces&&!interfaces.open);await open(interfaces);assert(interfaces.querySelector('.lr-function-existing-interface'));assert(interfaces.querySelector('.lr-required-domain'));assert.equal(interfaces.querySelectorAll('.lr-domain-binding').length,2);
   if(part.dataset.kind==='known-exact'){const premise=part.querySelector('.lr-proof-step');await open(premise);assert(!/cannot be matched exactly/.test(premise.textContent),premise.textContent);}
  }else{
   const nested=file.includes('nested'),bindings=part.querySelectorAll('.lr-function-call-layer').filter(node=>node.parentNode===part).flatMap(node=>node.querySelectorAll('.lr-function-call-binding'));assert.equal(bindings.length,nested?2:owner.type==='FnApplicationInStandardSupersetProof'&&file.includes('dependent-input')?2:1,file+': '+part.textContent);assert(bindings.every(node=>node.textContent.includes(' ← ')));
   if(nested){assert(bindings[0].textContent.includes('t ← 1'));assert(bindings[1].textContent.includes('x ← 2'));}
   for(const detail of part.querySelectorAll('.lr-function-call-inputs')){assert(!detail.open);if(file.includes('guard')||file.includes('dependent-input')){await open(detail);assert(detail.textContent.includes('≠')||detail.textContent.includes('≤')||detail.textContent.includes('fn'),detail.textContent);}}
   const uses=part.querySelector('.lr-function-property-uses');assert(uses&&!uses.open);await open(uses);const nativeUses=owner.fields.signature_returns||owner.fields.signature_uses;assert.equal(uses.querySelectorAll('.lr-function-property-use').length,nativeUses.length);
   if(file.endsWith('standard-return.json')&&file.includes('function-property-standard')){assert(part.textContent.includes('ℚ ⊆ ℂ'));assert(part.textContent.includes('ℝ ⊆ ℂ'));}
   if(file==='function-property-codomain-return.json')assert(uses.textContent.includes(locale==='zh'?'返回范围可以不同':'Return domains may differ'),uses.textContent);
  }
  const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);await open(tail);assert(!/not fully exported|未完整导出/.test(tail.textContent),file+': '+tail.textContent);
  const symbol=row.querySelector('[data-symbol]');if(symbol){await view.move(symbol);assert.strictEqual(view.root.querySelector('.lr-proof-popover'),card);assert.strictEqual(card.querySelector('.lr-function-property-proof'),part);}
  const link=part.querySelector('.lr-fact-link');if(link){await link.click();assert.equal(view.reader.getSelection().fact,link.dataset.fact);await view.root.querySelector('.lr-back').click();assert(view.root.querySelector('.lr-function-property-proof'));}
  if(locale==='zh'&&editable)views.push({file,text:part.textContent});if(editable){const input=view.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!view.root.querySelector('.lr-proof-popover'));}view.done();checked++;
 }
 for(const control of ['exact-source','exact-target','exact-match','exact-guard','standard-source','standard-path','standard-empty','standard-target','codomain-source','codomain-uses','codomain-domains','applied-application','applied-layers','applied-return','applied-domain']){
  const name=control.startsWith('exact')?'known-exact':control.startsWith('codomain')?'codomain-return':control.startsWith('applied')?'aliased-nested-standard-return':'standard-return',bundle=read(name),d=records(bundle),owner=d.frames(lastFact(bundle).evidence).find(node=>owners.includes(node.type));assert(owner,control);
  if(control==='exact-source')delete owner.fields.membership;if(control==='exact-target')delete owner.fields.target_signature;if(control==='exact-match')delete owner.fields.signature_match;if(control==='exact-guard')d.resolve(owner.fields.normalized_signature).fields.dom_facts=[{}];
  const row=d.resolve(owner.fields.signature_returns?.[0]);if(control==='standard-source')delete row.fields.source_set;if(control==='standard-path')delete row.fields.function_equal;if(control==='standard-empty')owner.fields.signature_returns=[];if(control==='standard-target')owner.fields.target_set={kind:'symbol_reference',symbol_id:'builtin:set:Z',name:'Z'};
  if(control==='codomain-source')delete owner.fields.cite_property_fact_id;if(control==='codomain-uses')delete owner.fields.signature_uses;if(control==='codomain-domains'){const use=owner.fields.signature_uses.map(d.resolve).find(node=>node.variant==='SameCallDomains');assert(use);delete use.fields.domains;}
  if(control.startsWith('applied')){const applied=d.resolve(row.fields.applied);if(applied.type!=='AppliedFnSetReturnSignature')continue;if(control==='applied-application')delete applied.fields.application;if(control==='applied-layers')applied.fields.layers=[];if(control==='applied-return')delete applied.fields.return_set;if(control==='applied-domain')delete d.resolve(applied.fields.layers[1]).fields.dom_facts;}
  const {view,part}=await show(bundle);assert(part,control);assert.equal(part.dataset.status,'incomplete',control+': '+part.textContent);assert(!part.querySelector('.lr-function-call-binding'));assert(!part.querySelector('.lr-function-property-uses'));view.done();checked++;
 }
 for(const name of ['standard-return','nested-codomain-return','aliased-nested-standard-return']){
  const bundle=read(name),d=records(bundle);for(const node of d.nodes.values()){if(node.type==='SignatureStandardReturnProof'||node.type==='FnApplicationInCodomainKnownSpecialPropertyProof')delete node.fields.applied;}
  const {view,part}=await show(bundle);assert(part);assert.equal(part.dataset.status,name.startsWith('aliased')?'incomplete':'retained');view.done();checked++;
 }
 assert.deepEqual([...families].sort(),owners.toSorted());console.log(JSON.stringify({passed:true,checked,families:[...families],bilingualEditableAndReadOnly:true,actualCallLayerCorrespondence:true,allNativeInterfaceUses:true,exactCompleteInterfaceComparison:true,sourceNavigationAndBack:true,stableSymbolCompartment:true,editInvalidation:true,wdLastAndClosed:true,legacyAliasFallbackHonest:true,nativeRecordsUnchanged:true,browserObserved:false,views},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
