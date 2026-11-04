'use strict';
// Observe the typed witness failure, never reconstruct discarded bindings.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw Error('Usage: node failed-witnesses.cjs <fixtures> [reader-source]');
const code=fs.readFileSync(process.argv[3]||path.join(__dirname,'../reader.js'),'utf8');
const cases={
 'exist-body':['BodyCheck','1 = 2'],'exist-count':['WitnessCountMismatch'],
 'exist-type':['WitnessType','−1 ∈ ℕ'],'atomic-type':['WitnessType','−1 ∈ ℕ'],
 'atomic-body':['BodyCheck','3 = 2'],'atomic-definition':['BadDefinition'],
 'atomic-unique':['BadDefinition'],'uniqueness':['Uniqueness'],
 'nonempty-member':['Membership','2 ∈ {1}'],'nonempty-object-wd':['ObjWd'],
 'nonempty-set-wd':['SetWd'],'nonempty-proof':['ProofBody'],
 'exist-wd':['ExistFactWellDefined'],'exist-object-wd':['WitnessObjWellDefined'],
 'atomic-argument':['PropArgumentType','{1} ∈ R'],'atomic-abstract':['AbstractProp'],
 'exist-proof':['ProofBody'],'atomic-proof':['ProofBody'],
 'witness-with-structure':['BodyCheck','(0, 1).x = 0'],
 'witness-uses-automatic-field-domain':['BodyCheck','(0, 1).x ∈ ℝ']
};
function read(name){const prefixed=path.join(directory,'witness-failure-'+name+'.json');return JSON.parse(fs.readFileSync(fs.existsSync(prefixed)?prefixed:path.join(directory,name+'.json'),'utf8'));}
function records(b){const nodes=new Map(b.evidence_nodes.map(row=>[row.id,row.node]));function resolve(v){const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};}return{nodes,resolve};}
function owner(b){return b.statements.find(s=>s.status==='rejected'&&s.statement_kind?.startsWith('Witness.'));}
function mount(b,locale,editable){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 return{...dom,root,reader,row(line){return root.querySelector('[data-line="'+line+'"]');},async hover(line,target=null,keyboard=false){const row=this.row(line);assert(row);target||=row.querySelector('.lr-source-code');if(keyboard)await row.querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'reader does not change sources, scopes, proof records or FactIds');reader.destroy();}};
}
async function inspect(name,locale,editable){
 const b=read(name),s=owner(b),v=mount(b,locale,editable),rows=v.root.querySelectorAll('.lr-code-row').length;
 assert.equal(b.run_result,'failure');let card=await v.hover(s.line),part=card?.querySelector('.lr-witness-failure');assert(part,name+': missing witness failure');assert.equal(part.dataset.status,'stage-retained',name+': '+part.textContent);assert.equal(part.dataset.stage,cases[name][0]);assert.equal(part.dataset.statement,s.id);
 assert(part.querySelector('.lr-witness-history'));assert(!part.querySelector('.lr-proof-substitutions,.lr-proof-requirements,.lr-witness-proof,.lr-definition-link'),'no invented binders, completed obligations or definition identity');
 if(cases[name][1]){const expected=cases[name][1].replace('−1','(-1)').replaceAll('ℕ','N').replaceAll('ℝ','R'),actual=part.textContent.replaceAll('ℕ','N').replaceAll('ℝ','R');assert(actual.includes(expected),name+': '+actual);}
 const tail=part.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert(tail.parentNode.children.at(-1)===tail,'own formation checks are final and closed');await tail.querySelector('summary').click();if(name.startsWith('nonempty-')&&name.endsWith('-wd')||['exist-wd','exist-object-wd'].includes(name))assert(tail.textContent.includes('0 ≠ 0'),tail.textContent);
 if(name.startsWith('witness-'))assert(part.querySelector('.lr-witness-formation-note'),'a substituted-body WD failure is not a binder/AutoOpen failure');
 if(name==='exist-count')assert(!/Required:|需要 \d/.test(part.textContent),'missing native counts are not reconstructed from source');
 if(['nonempty-proof','exist-proof','atomic-proof'].includes(name)){
  const prefix=part.querySelector('.lr-witness-prefix');assert(prefix&&!prefix.open);await prefix.querySelector('summary').click();const prior=prefix.querySelector('.lr-witness-prior-step');assert(prior.textContent.includes('1 = 1'));await prior.click();assert.equal(v.reader.getSelection().focusLine,s.line+1);await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().statement,s.id);
  part=v.root.querySelector('.lr-detail-body .lr-witness-failure');const failed=part.querySelector('.lr-witness-failed-step');assert(failed);await failed.click();assert.equal(v.reader.getSelection().focusLine,s.line+2);await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().statement,s.id);await v.close();card=await v.hover(s.line);part=card.querySelector('.lr-witness-failure');
 }
 await card.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert.equal(v.reader.getSelection().focusLine,s.line);assert.equal(v.reader.getSelection().fact,null);assert(v.root.querySelector('.lr-detail-body .lr-witness-failure'));await v.close();
 const keyword=v.row(s.line).querySelector('[data-keyword="witness"]');assert(keyword);card=await v.hover(s.line,keyword);assert(card.querySelector('.lr-witness-failure'));assert(card.querySelector('.lr-proof-symbol'));const symbol=v.row(s.line).querySelector('[data-symbol]');if(symbol){const kept=card.querySelector('.lr-witness-failure');assert(await v.hover(s.line,symbol)===card);assert(card.querySelector('.lr-witness-failure')===kept,'symbol help preserves the proof bubble');}await v.close();assert((await v.hover(s.line,null,true)).querySelector('.lr-witness-failure'));await v.close();
 assert.equal(s.produced_fact_ids.length,0);assert.equal(s.inferred_fact_ids.length,0);assert(!v.row(s.line).querySelector('.lr-inference-toggle'));assert.equal(v.root.querySelectorAll('.lr-code-row').length,rows);
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-proof-popover,.lr-witness-failure,.lr-diagnostic-point'));}v.done();
}
async function run(){let checks=0;
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const name of Object.keys(cases)){await inspect(name,locale,editable);checks++;}
 for(const control of ['root','owner','result','type','stage','prototype','payload','subject','reason','source','tokens','span','line','scope','scope-source','origin','publication','inference']){
  const b=read('witness-with-structure'),s=owner(b),d=records(b),root=d.resolve(s.evidence),dispatch=d.resolve(root.fields['0']),result=d.resolve(dispatch.fields['0']),failure=d.resolve(result.fields['0']);let failed=d.resolve(failure.fields['0']);while(failed.fields?.['0'])failed=d.resolve(failed.fields['0']);
  if(control==='root')root.variant='Fact';if(control==='owner')dispatch.variant='WitnessNonemptySet';if(control==='result')result.variant='Success';if(control==='type')failure.type='FutureFailure';if(control==='stage')failure.variant='FutureStage';if(control==='prototype')failure.variant=Object.create(null);if(control==='payload')delete failure.fields['0'];if(control==='subject')delete failed.fields.fact;if(control==='reason')delete failed.fields.reason;if(control==='source')s.source_id='foreign';if(control==='tokens')b.sources[0].tokens.find(token=>token.start_byte===s.start_byte).text='let';if(control==='span')s.start_byte++;if(control==='line')s.line--;if(control==='scope')s.scope_id='foreign';if(control==='scope-source')b.scopes.find(x=>x.id===s.scope_id).source_id='foreign';if(control==='origin')s.origin='generated';if(control==='publication')s.produced_fact_ids=['foreign'];if(control==='inference')s.inferred_fact_ids=['foreign'];
  const v=mount(b,'en',false);if(control==='source')await v.reader.selectStatement(s.id);else await v.hover(s.line);const part=v.root.querySelector('.lr-witness-failure');if(part){assert.equal(part.dataset.status,'incomplete',control);assert(!part.querySelector('.lr-proof-formula,.lr-witness-prefix,.lr-witness-failed-step'),control);}v.done();checks++;
 }
 for(const control of ['missing','count','foreign','order','child','child-source','child-owner','child-scope']){
  const b=read('nonempty-proof'),s=owner(b),d=records(b);let body=d.resolve(s.evidence);while(body.fields?.['0'])body=d.resolve(body.fields['0']);const child=b.statements.find(x=>x.id===body.fields.result.statement_id);
  if(control==='missing')delete body.fields.prior_steps;if(control==='count')body.fields.step_index='2';if(control==='foreign')body.fields.prior_steps[0].statement_id='foreign';if(control==='order')body.fields.prior_steps.push(body.fields.prior_steps[0]);if(control==='child')child.status='accepted';if(control==='child-source')child.source_id='foreign';if(control==='child-owner')child.parent_statement_id='foreign';if(control==='child-scope')child.scope_id=s.scope_id;
  const v=mount(b,'en',false),card=await v.hover(s.line),part=card?.querySelector('.lr-witness-failure');if(part){assert.equal(part.dataset.status,'incomplete',control);assert(!part.querySelector('.lr-witness-prefix,.lr-witness-failed-step'));}v.done();checks++;
 }
 const diagnostic=read('witness-with-structure');owner(diagnostic).failure.phase='auto_open_struct_layer';const dv=mount(diagnostic,'en',false),dc=await dv.hover(owner(diagnostic).line);assert.equal(dc.querySelector('.lr-witness-failure').dataset.stage,'BodyCheck','the typed native stage, not a derived diagnostic label, owns the explanation');dv.done();checks++;
 console.log(JSON.stringify({passed:true,checks,bilingualEditableReadOnly:true,typedStagesAndSubstitutedGoals:true,actualLocalPrefixAndFailureNavigation:true,keywordKeyboardSymbolPinAndBack:true,ownFormationLastAndClosed:true,missingHistoryNotReconstructed:true,malformedSourceAndOwnerFailClosed:true,noFailedPublication:true,editInvalidation:true,NativeUnchanged:true,browserObserved:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
