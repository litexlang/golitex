"use strict";
// Exact application names from actual exported proof records, never child rules.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs');
const directory=process.argv[2];if(!directory)throw new Error('Usage: node proof-rules.cjs <fixture-directory>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root();let timer=0;const timers=new Map();
 vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,console,setTimeout(fn){timers.set(++timer,fn);return timer;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,async hover(target){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});for(const [id,fn] of [...timers]){if(timers.has(id)){timers.delete(id);fn();}}return root.querySelector('.lr-proof-popover');}};
}
async function run(){
 const results=[];
 for(const locale of ['zh','en']){
  const bundle=fixture('lesson-sqrt-two-'+locale),before=JSON.stringify(bundle),view=mount(bundle,locale);
  const row=view.root.querySelector('[data-line="21"]');assert(row.textContent.includes('p / 2'));
  const card=await view.hover(row.querySelector('.lr-source-code')),application=card.querySelector('.lr-proof-application');assert(application,'the quotient proof names its actual rule');
  assert.equal(application.querySelector('code').textContent,'ExactIntegerDiv');assert(!application.textContent.includes('ExactIntegerQuotient'),'a different builtin fallback is not claimed');
  assert(application.textContent.includes('b ≠ 0'),'the full mathematical rule includes the nonzero guard');assert(application.textContent.includes('a / b ∈ ℤ'));
  assert(application.querySelector('.lr-proof-rule-result').textContent.includes('p / 2'),'the instantiated conclusion follows the rule');
  const context=card.querySelectorAll('.lr-proof-grounds .lr-fact-link').map(node=>node.textContent);assert(context.some(text=>text.includes('p ∈ ℤ')||text.includes('p ∈ Z')));assert(context.some(text=>text.includes('dvd(p, 2)')));
  assert(card.querySelector('.lr-proof-grounds').parentNode.childNodes.indexOf(application)>card.querySelector('.lr-proof-grounds').parentNode.childNodes.indexOf(card.querySelector('.lr-proof-grounds')),'context precedes the rule application');
  await card.querySelector('.lr-proof-pin').click();assert.equal(view.root.querySelector('.lr-detail-body .lr-proof-application code').textContent,'ExactIntegerDiv','pinned and hovered explanations share the actual application');
  assert.equal(JSON.stringify(bundle),before);view.reader.destroy();results.push({locale,exactStructuralRule:true,guardsAndContext:true,hoverAndPinAgree:true,unchangedExport:true});
 }
 const bundle=fixture('sqrt-two'),view=mount(bundle,'en'),equals=view.root.querySelectorAll('[data-line="7"] .lr-chain-equality');
 let card=await view.hover(equals[1]);assert.equal(card.querySelector('.lr-proof-application code').textContent,'Calculation');
 card=await view.hover(equals[0]);assert.equal(card.querySelector('.lr-proof-application code').textContent,'ArithmeticCongruence','a strategy is named as a strategy');assert(!card.querySelector('.lr-proof-application')?.textContent.includes('Calculation'),'a calculation in a premise is not the current equality rule');view.reader.destroy();
 const missing=fixture('sqrt-two');missing.rules=[];const noCatalogue=mount(missing,'en');card=await noCatalogue.hover(noCatalogue.root.querySelectorAll('[data-line="7"] .lr-chain-equality')[1]);assert.equal(card.querySelector('.lr-proof-application code').textContent,'Calculation','retained application identity survives a missing catalogue');noCatalogue.reader.destroy();
 const noIdentity=fixture('sqrt-two'),nodes=new Map(noIdentity.evidence_nodes.map(item=>[item.id,item.node]));for(const node of nodes.values())if(node.type==='EqualitySearchProofByBuiltinRule'&&node.variant==='Calculation')delete node.rule_id;
 const absent=mount(noIdentity,'en');card=await absent.hover(absent.root.querySelectorAll('[data-line="7"] .lr-chain-equality')[1]);assert(!card.querySelector('.lr-proof-application'),'a catalogue entry alone does not establish that the current proof used it');absent.reader.destroy();
 const assumedBundle=fixture('lesson-syllogism-en'),assumption=mount(assumedBundle,'en'),assumptionLine=assumedBundle.sources[0].content.split('\n').findIndex(line=>line.trim()==='$is_human(socrates)')+1;assert(assumptionLine);card=await assumption.hover(assumption.root.querySelector('[data-line="'+assumptionLine+'"] .lr-source-code'));assert(card);assert(card.textContent.includes('assumed'));assert(!card.querySelector('.lr-proof-application'));assumption.reader.destroy();
 const rejected=mount(fixture('predicate-membership-failure'),'en');card=await rejected.hover(rejected.root.querySelector('[data-line="1"] .lr-source-code'));assert(card.textContent.includes('has not established'));assert(!card.querySelector('.lr-proof-application'));rejected.reader.destroy();
 console.log(JSON.stringify({passed:true,results,exactEqualityRule:true,noChildRuleAttribution:true,missingCataloguePreservesName:true,missingIdentityNotGuessed:true,noSuccessRuleForFailureOrAssumption:true},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
