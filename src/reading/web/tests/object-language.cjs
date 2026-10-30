'use strict';
// Semantic operation help on real lexer spans, with native domain controls.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node object-language.cjs <object-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),catalogue=JSON.parse(fs.readFileSync(path.join(__dirname,'../../language_reference.json'),'utf8'));
const cases={
 'matrix-basic':['zero_matrix','identity_matrix','transpose','conjugate_transpose','trace','matrix'],
 'matrix-arithmetic':['matrix_add','matrix_sub','matrix_scale','matrix_mul','matrix_apply','matrix_power','diagonal_matrix','outer_product','cart_n'],
 'matrix-inverse':['det','matrix_minor','matrix_cofactor','matrix_adjugate','matrix_inverse','matrix_rank'],
 'inner-product':['inner_product','euclidean_norm','frobenius_norm','tuple'],
 'ranges':['range','closed_range','finite_set_size'], 'finite-sequences':['finite_seq'],
 'cartesian':['cart'], 'index-cartesian':['index_cart'], 'image':['fn_range'],
 'preimages':['preimage','preimage_set'], 'composition':['compose'], 'sum-product':['sum','product'],
 'finite-product':['finite_set_product'], 'ordered-fold':['reduce'],
 'set-fold':['finite_set_reduce','finite_set_sum'], 'finite-extrema':['finite_set_max','finite_set_min'],
 'sequence-limit':['seq','lim'], 'sequence-extrema':['limsup','liminf'],
 'function-limit':['fn_lim'], 'side-limits':['lim_left','lim_right'],
 'positive-infinity':['lim_pos_inf'], 'negative-infinity':['lim_neg_inf'],
 'real-bounds':['sup','inf'], 'derivative':['derivative'], 'integral':['integral']
};
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'object-'+name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,TextEncoder,URL,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,async hover(target,focus=false){assert(target);const selection=JSON.stringify(reader.getSelection());if(focus)await target.trigger('focus');else{dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}for(let round=0;round<3;round++)for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);fn();}assert.equal(JSON.stringify(reader.getSelection()),selection,'hover and focus do not select another fact');const tip=root.querySelector('.lr-proof-symbol:not([hidden])')||root.querySelector('.lr-token-help');assert(tip,target.textContent);return tip;},done(){assert.equal(JSON.stringify(bundle),before,'help never changes retained statements or verification evidence');reader.destroy();}};
}
async function run(){
 const observed=new Set();let hoverCount=0;
 for(const locale of ['zh','en']){
  for(const [name,spellings] of Object.entries(cases)){
   const bundle=fixture(name);assert.equal(bundle.run_result,'success',name);const view=mount(bundle,locale);
   for(const spelling of spellings){const token=view.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spelling);assert(token,name+': '+spelling);const tip=await view.hover(token),card=catalogue.entries[spelling];assert(card,spelling);assert(tip.textContent.includes(card.summary[locale]),tip.textContent);assert(tip.textContent.includes(card.notes[locale]),tip.textContent);assert.equal(tip.querySelector('.lr-reference-syntax').textContent,card.syntax);if(card.role)assert.equal(token.dataset.syntax,card.role);observed.add(spelling);hoverCount++;}
   const first=view.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spellings[0]),focused=await view.hover(first,true);assert(focused.textContent.includes(catalogue.entries[spellings[0]].summary[locale]),'keyboard focus has the same semantic help');view.done();
  }
  const command=mount(fixture('preimage-command'),locale),token=command.root.querySelector('[data-keyword="have by fn_preimage"]');assert(token);const tip=await command.hover(token);assert(tip.textContent.includes(locale==='zh'?'指定函数值':'specified function value'));command.done();
  for(const [name,spelling] of [['fractional-index','sum'],['noncommutative-fold','finite_set_reduce'],['missing-integral-proof','integral']]){
   const bundle=fixture(name),view=mount(bundle,locale);assert.equal(bundle.run_result,'failure');assert(view.root.querySelector('.lr-rejected'));const token=view.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spelling),tip=await view.hover(token);assert(tip.textContent.includes(catalogue.entries[spelling].notes[locale]));assert(!view.root.querySelector('.lr-proof-popover .lr-theorem-application'),'a domain failure does not become a successful theorem application');view.done();
  }
 }
 assert.equal(observed.size,56,'all newly documented named object operations are exercised');
 console.log(JSON.stringify({passed:true,namedOperations:observed.size,bilingualHovers:hoverCount,keyboardFocus:true,roleAccurate:true,domainRejectionsRetained:true,proofAndSourceRecordsUnchanged:true,contextualBraceAnchoring:'not covered'}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
