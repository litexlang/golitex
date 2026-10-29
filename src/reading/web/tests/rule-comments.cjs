'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];if(!directory)throw new Error('Usage: node rule-comments.cjs <fresh-fixture-directory>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),timers=new Map();let timer=0;
 vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,console,setTimeout(fn){timers.set(++timer,fn);return timer;},clearTimeout(id){timers.delete(id);}}));
 let checks=0;const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>{checks++;return bundle;}});
 return {...dom,root,reader,checks:()=>checks,async hover(target){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);fn();}return root.querySelector('.lr-proof-popover');}};
}
async function run(){
 let applications=0;
 for(const filename of fs.readdirSync(directory).filter(name=>name.endsWith('.json'))){
  const bundle=JSON.parse(fs.readFileSync(path.join(directory,filename),'utf8'));if(bundle.kind!=='reading')continue;
  for(const entry of bundle.evidence_nodes){const node=entry.node;if(!node.rule_id?.startsWith('builtin.'))continue;for(const locale of ['en','zh'])assert(node.comment?.[locale]?.name&&node.comment[locale].message,filename+': '+node.rule_id+' '+locale);applications++;}
 }
 assert(applications>10,'actual verified rules, not a handcrafted explanation fixture');
 const bundle=fixture('builtin'),before=JSON.stringify(bundle),id='builtin.DvdFactSearchProofByBuiltinRule::One',actual=bundle.evidence_nodes.find(entry=>entry.node.rule_id===id).node;
 const view=mount(bundle,'zh');for(const locale of ['zh','en']){view.reader.setLanguage(locale);const card=await view.hover(view.root.querySelector('[data-line="3"] .lr-source-code')),application=card.querySelector('.lr-proof-application');assert.equal(application.dataset.rule,id);assert.equal(application.querySelector('.lr-proof-rule-message').textContent,actual.comment[locale].message);assert.equal(application.querySelector('.lr-proof-rule-title').textContent,actual.comment[locale].name);}
 assert.equal(view.checks(),0);assert.equal(JSON.stringify(bundle),before);view.reader.destroy();
 const legacy=fixture('builtin');for(const entry of legacy.evidence_nodes)delete entry.node.comment;const older=mount(legacy,'zh'),card=await older.hover(older.root.querySelector('[data-line="3"] .lr-source-code'));assert(card.querySelector('.lr-proof-rule-message').textContent);older.reader.destroy();
 console.log(JSON.stringify({passed:true,applications,bilingualOnActualNodes:true,languageSwitchWithoutReverification:true,legacyCatalogueFallback:true,unchangedExport:true},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
