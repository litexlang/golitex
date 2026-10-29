'use strict';
// Retained definition applications, via public source hover and navigation.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node definition-proofs.cjs <definition-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
function fixture(name){return JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8'));}
function records(bundle){const nodes=new Map(bundle.evidence_nodes.map(item=>[item.id,item.node]));const resolve=value=>{while(value?.kind==='evidence_reference')value=nodes.get(value.evidence_id);return value||{};};function frames(value){const found=[],seen=new Set();let node=resolve(value);while(node&&!seen.has(node)){seen.add(node);found.push(node);const next=node.fields?.searched_proof||node.fields?.['0'];if(!next)break;node=resolve(next);}return found;}return {nodes,resolve,frames};}
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,console,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,async hover(fact,formation=true){const row=root.querySelector('[data-line="'+fact.line+'"]');assert(row);dom.document.elementFromPoint=()=>row.querySelector('.lr-source-code');await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);fn();}const card=root.querySelector('.lr-proof-popover');assert(card);if(formation){const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);}return card;},done(){assert.equal(JSON.stringify(bundle),before,'presentation never changes retained evidence');reader.destroy();}};
}
async function run(){
 for(const locale of ['zh','en']){
  const b=fixture('reciprocal'),data=records(b),fact=b.facts.find(f=>f.is_primary&&f.role==='verified'),view=mount(b,locale),card=await view.hover(fact),app=card.querySelector('.lr-definition-application');assert(app);assert(app.textContent.includes('x = 2'));assert(app.textContent.includes('reciprocal(2) = (1 / 2)'));assert(app.textContent.includes(locale==='zh'?'两边是同一表达式':'both sides are the same expression'));
  const expansion=[...data.nodes.values()].find(n=>n.type==='AnonymousFunctionBodyExpansionProof'),source=data.resolve(data.resolve(expansion.fields.function_body).fields['0']).fields.path[0][2].fact_id;assert.equal(app.querySelector('.lr-proof-definition-source .lr-fact-link').dataset.fact,source);
  const tail=card.querySelector('.lr-atomic-wd');await tail.querySelector('summary').click();assert(tail.textContent.includes('2 ≠ 0'),'the guard remains in the closed final formation section');const nonzero=tail.querySelectorAll('.lr-proof-step').find(item=>item.querySelector('summary').textContent.includes('2 ≠ 0'));await nonzero.querySelector('summary').click();assert(!nonzero.textContent.includes('gives equal values'));assert(!nonzero.textContent.includes('结果相等'));
  await app.querySelector('.lr-fact-link').click();assert.equal(view.reader.getSelection().fact,source);await view.root.querySelector('.lr-back').click();assert.equal(view.reader.getSelection().fact,fact.id);assert(view.root.querySelector('.lr-detail-body .lr-definition-application'));view.done();
  const predicate=fixture('predicate'),pf=predicate.facts.find(f=>f.is_primary&&f.role==='verified'),pv=mount(predicate,locale),pc=await pv.hover(pf),pa=pc.querySelector('.lr-predicate-application');assert(pa);assert(pa.textContent.includes('x = 1'));assert(pa.querySelector('.lr-definition-link'));assert.equal(pc.querySelectorAll('.lr-proof-requirements .lr-proof-step').length,2);await pa.querySelector('.lr-definition-link').click();assert.equal(pv.reader.getSelection().statement,predicate.statements.find(s=>s.statement_kind==='Definition.DefPropStmt').id);pv.done();
 }
 for(const locale of ['zh','en']){
  const bundle=fixture('by-def'),data=records(bundle),fact=bundle.facts.find(f=>f.text==='$nonnegative(3)'),view=mount(bundle,locale),card=await view.hover(fact);assert(card.querySelector('.lr-predicate-application').textContent.includes('x = 3'));const condition=card.querySelectorAll('.lr-proof-requirements .lr-proof-step').find(item=>item.textContent.includes('3 ≥ 0'));assert(condition);await condition.querySelector('summary').click();assert(!condition.textContent.includes('cannot be matched'));view.done();
 }
 const guarded=fixture('body-guard'),gv=mount(guarded,'en'),gf=guarded.facts.find(f=>f.is_primary&&f.role==='verified'&&f.line===4),gc=await gv.hover(gf);assert(gc.querySelector('.lr-definition-application').textContent.includes('x = 2'));const guard=gc.querySelector('.lr-atomic-wd');await guard.querySelector('summary').click();assert(guard.textContent.includes('2 ≠ 0'),'the selected narrower function body retains its own guard');gv.done();
 for(const name of ['missing-body-guard','wrong-reciprocal']){
  const bundle=fixture(name),view=mount(bundle,'en');assert.equal(bundle.run_result,'failure');const card=await view.hover({line:name==='wrong-reciprocal'?2:4},false);assert(!card.querySelector('.lr-definition-application'));assert(!card.querySelector('.lr-proof-application'));assert(/not established|could not|failed|cannot/.test(card.textContent),card.textContent);view.done();
 }
 for(const [name,needle] of [['nested','x = inner(x)'],['both','x = 2'],['alias','x = 4']]){
  const bundle=fixture(name),data=records(bundle),fact=bundle.facts.find(f=>f.is_primary&&f.role==='verified'&&f.line&&data.frames(f.evidence).some(n=>n.variant==='ByObjectDefinition')),view=mount(bundle,'en'),card=await view.hover(fact),app=card.querySelector('.lr-definition-application');assert(app,name);assert(app.textContent.includes(needle),app.textContent);if(name==='both')assert.equal(app.querySelectorAll('.lr-definition-expansion').length,4,'both curried sides retain each application');if(name==='alias'){const residual=app.querySelector('.lr-proof-step');assert(residual);await residual.querySelector('summary').click();assert(residual.textContent.includes('Exact calculation'));}view.done();
 }
 for(const name of ['tuple','fn-tuple','codomain']){
  const bundle=fixture(name),data=records(bundle),fact=bundle.facts.find(f=>f.is_primary&&f.role==='verified'&&f.line&&data.frames(f.evidence).some(n=>n.variant==='ByKnownSpecialProperty')),view=mount(bundle,'en'),app=(await view.hover(fact)).querySelector('.lr-special-application');assert(app,name);assert(app.querySelector('.lr-fact-link'));if(name==='tuple')assert(app.textContent.includes('Select coordinate 1:'));if(name==='fn-tuple'){assert(app.textContent.includes('c = a'));assert(app.textContent.includes('d = b'));}if(name==='codomain')assert(app.textContent.includes('x = a'));view.done();
 }
 const alias=fixture('alias'),av=mount(alias,'en'),af=alias.facts.find(f=>f.is_primary&&f.text==='h(4) = 5'),ac=await av.hover(af),transport=ac.querySelector('.lr-equality-transport');assert(transport);assert(transport.querySelector('.lr-fact-link'));const bridge=transport.querySelector('.lr-proof-step');assert(bridge);await bridge.querySelector('summary').click();assert(bridge.querySelector('.lr-atomic-wd'),'the separately checked bridge has its own closed formation tail');assert(!bridge.querySelector('.lr-atomic-wd').open);av.done();
 for(const kind of ['missingBody','arity','noExpansion','missingResidual','wrongResidualFact']){
  const b=fixture('reciprocal'),data=records(b),fact=b.facts.find(f=>f.is_primary&&f.role==='verified'),expansion=[...data.nodes.values()].find(n=>n.type==='AnonymousFunctionBodyExpansionProof'),normalization=[...data.nodes.values()].find(n=>n.type==='FunctionBodyNormalizationProof'),detail=data.frames(fact.evidence).find(n=>n.type==='ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof');
  if(kind==='missingBody')delete expansion.fields.function_body;
  if(kind==='arity'){let app=data.resolve(expansion.fields.application);app=data.resolve(app.fields['0']);app.fields.body=[[]];}
  if(kind==='noExpansion')normalization.fields.expansions=[];
  if(kind==='missingResidual')delete detail.fields.residual_equal;
  if(kind==='wrongResidualFact'){const result=data.frames(detail.fields.residual_equal).find(n=>n.type==='VerifyEqualitySuccess');delete result.fields.fact;}
  const view=mount(b,'en'),app=(await view.hover(fact)).querySelector('.lr-definition-application');assert(app);
  if(['missingBody','arity'].includes(kind))assert(!app.textContent.includes('x = 2'));
  assert(/incomplete|not.*exported/.test(app.textContent),app.textContent);view.done();
 }
 console.log(JSON.stringify({passed:true,bilingualReciprocalAndPredicate:true,definitionCitationAndReturn:true,nestedCurriedAliasAndResidual:true,tupleAndFunctionCodomain:true,missingEvidenceNotGuessed:true,wdLastAndClosed:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
