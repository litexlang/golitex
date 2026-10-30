'use strict';
// All native multivariable names, through public source hover/focus events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node multivariable-language.cjs <multivariable-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),catalogue=JSON.parse(fs.readFileSync(path.join(__dirname,'../../language_reference.json'),'utf8'));
const selectors=Object.entries(catalogue.ast_surfaces.Obj).filter(([key])=>/Obj\.(DerivativeOperator\.(Partial|ScalarDifferential|TotalDifferential|Gradient|Jacobian|Hessian|Divergence|Curl|Laplacian)|LimitOperator\.Multivariable)/.test(key)).flatMap(([,keys])=>keys);
const predicates=catalogue.ast_surfaces.Fact['Fact.AtomicFact.MultivariableAnalysisFact'];
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'multivariable-'+name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,TextEncoder,URL,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,async hover(target,focus=false){assert(target);const selection=JSON.stringify(reader.getSelection());if(focus)await target.trigger('focus');else{dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}for(let round=0;round<3;round++)for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);fn();}assert.equal(JSON.stringify(reader.getSelection()),selection,'semantic help does not select a proof');const tip=root.querySelector('.lr-proof-symbol:not([hidden])')||root.querySelector('.lr-token-help');assert(tip,target.textContent);return tip;},done(){assert.equal(JSON.stringify(bundle),before,'help does not modify source, accepted facts or evidence');reader.destroy();}};
}
async function run(){
 assert.equal(selectors.length,11);assert.equal(predicates.length,16);
 let hovers=0;
 for(const locale of ['zh','en']){
  const bundle=fixture('calculus');assert.equal(bundle.run_result,'success');const view=mount(bundle,locale);
  for(const [role,names] of [['function',selectors],['predicate',predicates]]){
   for(const name of names){
    const token=view.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===name),card=catalogue.entries[name];assert(token,name);assert.equal(token.dataset.syntax,role,name);
    for(const focus of [false,true]){
     const tip=await view.hover(token,focus);assert(tip.textContent.includes(card.kind[locale]),name);assert(tip.textContent.includes(card.summary[locale]),name);assert(tip.textContent.includes(card.notes[locale]),name);assert.equal(tip.querySelector('.lr-reference-syntax').textContent,card.syntax);hovers++;
    }
   }
  }
  view.done();
  for(const [name,spelling] of [['wrong-coordinate','has_partial_derivative_at'],['without-proof','lim_multi_at']]){
   const rejected=fixture(name);assert.equal(rejected.run_result,'failure');const rv=mount(rejected,locale);assert(rv.root.querySelector('.lr-rejected'));
   const token=rv.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spelling),tip=await rv.hover(token);assert(tip.textContent.includes(catalogue.entries[spelling].notes[locale]));assert(!rv.root.querySelector('.lr-proof-popover .lr-theorem-application'),'domain or existence failure is not a theorem success');rv.done();
  }
 }
 console.log(JSON.stringify({passed:true,selectors:11,predicates:16,bilingualHoverAndFocus:hovers,exactSignatures:true,failedCoordinateAndMissingCandidate:true,sourceAndEvidenceUnchanged:true,browserGeometry:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
