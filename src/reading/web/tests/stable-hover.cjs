"use strict";
// Public pointer/focus paths over real retained records, with a controlled clock.
// This tests lifecycle and identity, not browser layout or pointer hit geometry.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs');
const directory=process.argv[2];if(!directory)throw new Error('Usage: node stable-hover.cjs <fixture-directory>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
function mount(name,locale,editable=true){
 const bundle=JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8')),before=JSON.stringify(bundle),dom=createDOM(),root=dom.root();
 let now=0,next=0;const timers=new Map();
 const setTimeout=(fn,ms)=>{timers.set(++next,{fn,at:now+ms});return next;},clearTimeout=id=>timers.delete(id);
 vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,setTimeout,clearTimeout,console}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const source=bundle.sources.find(item=>item.id===bundle.entry_source_id)||bundle.sources[0];
 return {...dom,root,reader,bundle,before,
  row(text){const line=source.content.split('\n').findIndex(line=>line.trim()===text)+1;assert(line,text);return root.querySelector('[data-line="'+line+'"]');},
  async move(target){if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');},
  async tick(ms){const end=now+ms;for(;;){const due=[...timers].filter(([,value])=>value.at<=end).sort((a,b)=>a[1].at-b[1].at)[0];if(!due)break;now=due[1].at;timers.delete(due[0]);await due[1].fn();await Promise.resolve();}now=end;},
  card(){return root.querySelector('.lr-proof-popover');},
  done(){assert.equal(JSON.stringify(bundle),before,'hover never changes reading JSON');reader.destroy();assert(!root.querySelector('.lr-proof-popover'));}
 };
}
const token=(row,text)=>row.querySelectorAll('[data-syntax]').find(item=>item.textContent.trim()===text);
async function run(){
 const results=[];
 for(const locale of ['zh','en'])for(const editable of [true,false]){
  const view=mount('lesson-sets-'+locale,locale,editable),row=view.row('2 $in intersect({1, 2}, {2, 3})'),symbol=token(row,'intersect'),membership=token(row,'in');assert(symbol&&membership);
  await view.move(row.querySelector('.lr-source-code'));await view.tick(300);assert(!view.card(),'passing over a sentence does not immediately open a card');
  await view.move(symbol);await view.tick(160);
  const card=view.card();assert(card,'moving within a sentence must not restart its dwell timer');
  const proof=card.querySelector('.lr-proof-evidence'),info=card.querySelector('.lr-proof-symbol');assert(proof&&info&&!info.hidden,'proof and symbol information coexist');
  assert(info.textContent.includes('∩'),'intersection documentation belongs to the hovered operator');
  const condition=proof.querySelector('.lr-proof-step');assert(condition);await condition.querySelector('summary').click();proof.scrollTop=42;
  await view.move(membership);assert.strictEqual(view.card(),card,'symbol movement retains the floating container');assert.strictEqual(card.querySelector('.lr-proof-evidence'),proof,'proof DOM is retained');
  assert(condition.open,'expanded proof conditions stay expanded');assert.equal(proof.scrollTop,42);assert(info.textContent.includes('∈'));
  assert(!view.root.querySelector('.lr-token-help'),'no competing tooltip covers the proof');
  assert.equal(membership.getAttribute('aria-describedby'),info.id,'keyboard focus can identify the symbol compartment');
  await view.move(row.querySelector('.lr-source-code'));assert.strictEqual(view.card(),card);await view.tick(500);assert.strictEqual(view.card(),card);
  await row.trigger('pointerleave');await view.tick(150);await card.trigger('pointerenter');await view.tick(400);assert.strictEqual(view.card(),card,'crossing the source/card gap keeps the card available');
  await view.move(view.row('? not 1 $in intersect({1, 2}, {2, 3})').querySelector('.lr-source-code'));await view.tick(150);await card.trigger('pointerenter');await view.tick(460);assert.strictEqual(view.card(),card,'entering the card cancels an incidental neighboring-sentence candidate');
  await card.trigger('pointerleave');await view.tick(301);assert(!view.card(),'leaving both source and preview closes it');
  await view.move(symbol);await view.tick(460);assert(view.card(),'starting directly on an operation still opens the fact proof');
  const close=view.card().querySelector('.lr-explanation-close');close.focus();await close.click();assert(!view.card());assert.strictEqual(view.document.activeElement,editable?view.root.querySelector('.lr-ide-input'):row.querySelector('.lr-line-number'),'closing a sentence card restores a focusable source control');await view.tick(460);assert(!view.card(),'restoring focus does not reopen the preview');
  await view.move(symbol);await view.tick(460);await view.root.trigger('keydown',{key:'Escape'});assert(!view.card());view.done();
  results.push({locale,editable,stableSentenceDwell:true,retainedProofAndDisclosure:true,symbolCompartment:true,enterAndDismiss:true});
 }
 const definition=mount('lesson-definitions-en','en'),defined=definition.row('by def $nonnegative(3)'),predicate=token(defined,'nonnegative');assert(predicate);
 await definition.move(predicate);await definition.tick(460);let card=definition.card();assert(card.querySelector('.lr-proof-evidence').textContent.includes('Substitute the arguments'));
 assert(card.querySelector('.lr-proof-symbol .lr-predicate-definition').textContent.includes('nonnegative(x)'));
 await definition.move(token(defined,'by def'));assert.strictEqual(definition.card(),card);assert(card.querySelector('.lr-proof-symbol').textContent.includes('by def'));
 const edit=definition.root.querySelector('.lr-ide-input');edit.value+=' ';await edit.trigger('input');assert(!definition.card(),'edits invalidate both proof and symbol data');definition.done();
 const equality=mount('sqrt-two','en'),equals=equality.root.querySelectorAll('.lr-code-row[data-line="7"] .lr-chain-equality'),relations=[];
 for(const equal of equals){await equality.move(equal);await equality.tick(460);relations.push(equality.card().querySelector('.lr-proof-part .lr-formula').textContent);}
 assert.equal(new Set(relations).size,3,'adjacent equalities keep their own proof');equality.done();
 const failed=mount('predicate-membership-failure','en'),rejected=failed.row('1 $in intersect({1, 2}, {2, 3})');await failed.move(token(rejected,'intersect'));await failed.tick(460);
 card=failed.card();assert(card.querySelector('.lr-proof-evidence').textContent.includes('has not established'));assert(card.querySelector('.lr-proof-symbol').textContent.includes('∩'));failed.done();
 const assumed=mount('lesson-syllogism-en','en'),hypothesis=assumed.row('$is_human(socrates)');await assumed.move(token(hypothesis,'socrates'));await assumed.tick(460);card=assumed.card();assert(card.querySelector('.lr-proof-evidence').textContent.includes('assumed'));assert(card.querySelector('.lr-proof-symbol').textContent.includes('socrates'));assumed.done();
 console.log(JSON.stringify({passed:true,results,definitionAndKeywordHelp:true,exactEqualitySteps:true,failedAndLocalStatusPreserved:true},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
