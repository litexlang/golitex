'use strict';
// Actual exported certificates through the public reader and DOM events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node atomic-wd.cjs <fixture-directory>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),timers=new Map();let timer=0;
 vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,console,setTimeout(fn){timers.set(++timer,fn);return timer;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,async hover(target){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);fn();}return root.querySelector('.lr-proof-popover');}};
}
function assertTail(card){
 const tail=card.querySelector('.lr-atomic-wd');assert(tail,'atomic verification has a WD tail');assert(!tail.open,'WD is collapsed by default');assert.equal(tail.parentNode.children.at(-1),tail,'WD follows all proof routes, including early returns');assert.equal(tail.querySelectorAll('.lr-proof-step').length,0,'WD details are lazy');return tail;
}
async function run(){
 const receipt=[];
 for(const locale of ['zh','en']){
  const bundle=fixture('lesson-sqrt-two-'+locale),before=JSON.stringify(bundle),view=mount(bundle,locale);
  const card=await view.hover(view.root.querySelector('[data-line="21"] .lr-source-code')),tail=assertTail(card);
  assert(!card.textContent.includes('外层检查负责'));assert(!card.textContent.includes('enclosing verification'));
  await tail.querySelector('summary').click();assert(tail.open);
  const condition=tail.querySelectorAll('.lr-proof-step').find(node=>/2\s*≠\s*0/.test(node.querySelector('summary').textContent));assert(condition,'the actual nonzero-denominator proof is retained, including closed calculations');
  await condition.querySelector('summary').click();assert(condition.open);assert(!condition.textContent.includes('cannot be matched'));assert(!condition.textContent.includes('准确对应'));assert(condition.querySelector('.lr-proof-summary')||condition.querySelector('.lr-proof-application'),'the retained condition has its own proof explanation');assert.equal(JSON.stringify(bundle),before);view.reader.destroy();receipt.push({locale,collapsed:true,last:true,nonzeroProof:true,unchangedExport:true});
 }
 for(const [name,line] of [['known',8],['builtin',3],['strategy',8],['named-strategy',15],['forall-en',9]]){
  const bundle=fixture(name),view=mount(bundle,'en');let target=view.root.querySelector('[data-line="'+line+'"] .lr-source-code');
  if(name==='named-strategy')target=view.root.querySelectorAll('.lr-source-code').find(node=>node.textContent.trim()==='$is_one(a)');
  if(name==='forall-en')target=view.root.querySelectorAll('.lr-source-code').filter(node=>node.textContent.includes('$is_mortal(socrates)')&&!node.textContent.includes('=>')).at(-1);
  assert(target,name);const card=await view.hover(target);assert(card,name);assertTail(card);view.reader.destroy();receipt.push({name,collapsedAndLast:true});
 }
 const equality=mount(fixture('sqrt-two'),'en'),card=await equality.hover(equality.root.querySelectorAll('[data-line="7"] .lr-chain-equality')[1]);assertTail(card);equality.reader.destroy();
 const rejected=mount(fixture('predicate-membership-failure'),'en'),rejectedCard=await rejected.hover(rejected.root.querySelector('[data-line="1"] .lr-source-code'));assertTail(rejectedCard);assert(rejectedCard.textContent.includes('not established'));assert(!rejectedCard.querySelector('.lr-proof-application'),'a successful domain check does not prove the rejected fact');await rejectedCard.querySelector('.lr-atomic-wd summary').click();assert(!rejectedCard.querySelector('.lr-atomic-wd').textContent.includes('not fully exported'));rejected.reader.destroy();
 const missing=fixture('lesson-sqrt-two-en');for(const entry of missing.evidence_nodes)if(['VerifyEqualitySuccess','VerifyAtomicExceptEqualityFactSuccess'].includes(entry.node.type))delete entry.node.fields.well_defined_proof;
 const absent=mount(missing,'en'),missingCard=await absent.hover(absent.root.querySelector('[data-line="21"] .lr-source-code')),tail=assertTail(missingCard);await tail.querySelector('summary').click();assert(tail.textContent.includes('not fully exported'));assert.equal(tail.querySelectorAll('.lr-proof-step').length,0);absent.reader.destroy();
 console.log(JSON.stringify({passed:true,receipt,equalityTail:true,missingDataHonest:true,rejectedFactKeepsSuccessfulWDSeparate:true},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
