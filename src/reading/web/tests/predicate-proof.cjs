"use strict";
// Actual exported proof records; unmodified reader and source hover handlers.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs');
const directory=process.argv[2];if(!directory)throw new Error('Usage: node predicate-proof.cjs <fixture-directory>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),delay=()=>new Promise(resolve=>setTimeout(resolve,480));
function fixture(name){return JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8'));}
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),source=bundle.sources.find(source=>source.id===bundle.entry_source_id)||bundle.sources[0];
 vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,setTimeout,clearTimeout,console}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,row(text){const line=source.content.split('\n').findIndex(line=>line.trim()===text)+1;assert(line,text);return root.querySelector('[data-line="'+line+'"]');},async hover(row){const token=row.querySelectorAll('.lr-syntax-predicate').find(token=>token.textContent.trim()!=='$');assert(token);dom.document.elementFromPoint=()=>token;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});await delay();const card=root.querySelector('.lr-proof-popover');assert(card);return card;}};
}
async function run(){
 const results=[];
 for(const locale of ['zh','en']){
  const bundle=fixture('lesson-sets-'+locale),before=JSON.stringify(bundle),view=mount(bundle,locale);
  let card=await view.hover(view.row('2 $in intersect({1, 2}, {2, 3})'));
  assert(card.querySelector('.lr-predicate-definition').textContent.includes('x ∈ A ∩ B'));
  assert(!card.textContent.includes(locale==='zh'?'此类证明的逐步解说尚未提供':'step-by-step explanation of this proof form is not available'));
  const requirements=card.querySelectorAll('.lr-proof-step');assert.equal(requirements.length,2);
  assert(requirements[0].textContent.includes('2 ∈ {1, 2}'));assert(requirements[1].textContent.includes('2 ∈ {2, 3}'));
  for(const item of requirements){await item.querySelector('summary').click();assert(item.textContent.includes(locale==='zh'?'列出的元素':'listed elements'));}
  card=await view.hover(view.row('? not 1 $in intersect({1, 2}, {2, 3})'));
  assert(card.querySelector('.lr-predicate-definition'));assert(card.textContent.includes(locale==='zh'?'反证法':'Proof by contradiction'));
  assert(card.textContent.includes(locale==='zh'?'反证假设':'Contradiction assumption'));
  assert(card.querySelector('.lr-proof-grounds .lr-fact-link').textContent.includes(locale==='zh'?'局部假设':'Local hypothesis'));
  assert.equal(card.querySelectorAll('.lr-proof-step').length,2);
  for(const item of card.querySelectorAll('.lr-proof-step'))await item.querySelector('summary').click();
  assert(card.textContent.includes(locale==='zh'?'每个元素都不相等':'differs from every listed element'));
  assert.equal(JSON.stringify(bundle),before,'display enrichment does not mutate exported facts');view.reader.destroy();

  const definition=fixture('lesson-definitions-'+locale),original=JSON.stringify(definition),defined=mount(definition,locale);
  card=await defined.hover(defined.row('by def $nonnegative(3)'));
  const meaning=card.querySelector('.lr-predicate-definition');assert(meaning);assert(meaning.textContent.includes('nonnegative(x)'));assert(/x ∈ (?:R|ℝ)/.test(meaning.textContent),meaning.textContent);assert(meaning.textContent.includes('x ≥ 0'));
  assert(card.textContent.includes(locale==='zh'?'将实参代入谓词定义':'Substitute the arguments into the predicate definition'));
  assert.equal(card.querySelectorAll('.lr-proof-step').length,2);assert.equal(JSON.stringify(definition),original);defined.reader.destroy();
  const assumed=mount(fixture('lesson-syllogism-'+locale),locale);card=await assumed.hover(assumed.row('$is_human(socrates)'));assert(card.querySelector('.lr-predicate-definition'),'a local predicate assumption retains its declared interface');assert(card.textContent.includes(locale==='zh'?'假定此条件成立':'condition is assumed'));assumed.reader.destroy();
  results.push({locale,definitionAndProofTogether:true,intersectionRequirementsAndProofs:true,contradictionScopePreserved:true,exportUnchanged:true});
 }
 const broken=fixture('lesson-sets-en'),nodes=new Map(broken.evidence_nodes.map(item=>[item.id,item.node]));
 const resolve=value=>value?.kind==='evidence_reference'?resolve(nodes.get(value.evidence_id)):value;
 const fact=broken.facts.find(fact=>fact.is_primary&&fact.text==='2 $in intersect({1, 2}, {2, 3})');let node=resolve(fact.evidence);
 while(node&&!Array.isArray(node.fields?.proof_of_requirement_facts))node=resolve(node.fields?.searched_proof||node.fields?.['0']);assert(node);
 node.fields.proof_of_requirement_facts[0]=node.fields.proof_of_requirement_facts[1];
 const degraded=mount(broken,'en'),card=await degraded.hover(degraded.row('2 $in intersect({1, 2}, {2, 3})'));
 const condition=card.querySelector('.lr-proof-step');await condition.querySelector('summary').click();assert(condition.textContent.includes('No proof record can be matched exactly'));degraded.reader.destroy();
 const rejected=mount(fixture('predicate-membership-failure'),'zh'),failure=await rejected.hover(rejected.row('1 $in intersect({1, 2}, {2, 3})'));
 assert(failure.querySelector('.lr-predicate-definition'));assert(failure.textContent.includes('当前证明尚未建立这个结论'));assert(!failure.textContent.includes('这一步已验证'));rejected.reader.destroy();
 const known=mount(fixture('predicate-membership-known'),'en'),knownCard=await known.hover(known.row('2 $in intersect({1, 2}, {2, 3})'));assert(knownCard.querySelector('.lr-predicate-definition'));assert.equal(knownCard.querySelectorAll('.lr-proof-step').length,2,'the direct builtin-rule route retains both membership proofs');known.reader.destroy();
 console.log(JSON.stringify({passed:true,results,wrongRequirementProofRejected:true},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
