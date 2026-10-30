'use strict';
// Postfix and structural spellings on native source, including legacy exports.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node symbol-language.cjs <symbol-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),catalogue=JSON.parse(fs.readFileSync(path.join(__dirname,'../../language_reference.json'),'utf8'));
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'symbol-'+name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,TextEncoder,URL,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,async hover(target,focus=false){assert(target);const selection=JSON.stringify(reader.getSelection());if(focus)await target.trigger('focus');else{dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}for(let round=0;round<3;round++)for(const [id,fn]of [...timers])if(timers.has(id)){timers.delete(id);fn();}assert.equal(JSON.stringify(reader.getSelection()),selection);const tip=root.querySelector('.lr-proof-symbol:not([hidden])')||root.querySelector('.lr-token-help');assert(tip,target.textContent);return tip;},done(){assert.equal(JSON.stringify(bundle),before,'help leaves native source, facts and evidence untouched');reader.destroy();}};
}
async function run(){
 const cases=[['factorial','!','factorial'],['factorial','factorial','factorial'],['structure','&','obj:struct_type'],['field','.','obj:field'],['template','\\','obj:template'],['closed-range','...','closed_range']];let checks=0;
 for(const locale of ['zh','en'])for(const hints of [true,false]){
  for(const [name,spelling,key] of cases){
   const bundle=fixture(name);assert.equal(bundle.run_result,'success',name);if(!hints)for(const statement of bundle.statements)delete statement.expression_hints;
   const view=mount(bundle,locale),token=view.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spelling),card=catalogue.entries[key];assert(token,name+': '+spelling);
   for(const focus of [false,true]){const tip=await view.hover(token,focus);assert(tip.textContent.includes(card.summary[locale]),spelling);assert(tip.textContent.includes(card.notes[locale]),spelling);checks++;}
   view.done();
  }
  const unique=mount(fixture('unique'),locale),token=unique.root.querySelectorAll('[data-syntax]').find(node=>node.textContent==='∃!');assert(token);assert.equal(token.dataset.keyword,'exist!');const help=await unique.hover(token);assert(help.textContent.includes(catalogue.entries['exist!'].summary[locale]));assert(!help.textContent.includes(catalogue.entries.factorial.summary[locale]),'unique existence is not factorial');unique.done();
 }
 for(const locale of ['zh','en'])for(const name of ['factorial-negative','factorial-fractional','factorial-wrong-value']){
  const bundle=fixture(name);assert.equal(bundle.run_result,'failure');const view=mount(bundle,locale),token=view.root.querySelectorAll('[data-syntax]').find(node=>['factorial','!'].includes(node.textContent));assert(view.root.querySelector('.lr-rejected'));const tip=await view.hover(token);assert(tip.textContent.includes(catalogue.entries.factorial.notes[locale]));assert(!view.root.querySelector('.lr-proof-popover .lr-theorem-application'));view.done();
 }
 console.log(JSON.stringify({passed:true,bilingualHoverFocus:checks,postfixAndNamedFactorial:true,structFieldTemplateAndRange:true,withoutExpressionHints:true,uniqueExistenceUnchanged:true,negativeFractionalWrongValueRejected:true,sourceAndEvidenceUnchanged:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
