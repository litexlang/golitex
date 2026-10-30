'use strict';
// Repeated AST-owned positions, never a borrowed same-spelled brace or fact id.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node repeated-language.cjs <repeated-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),catalogue=JSON.parse(fs.readFileSync(path.join(__dirname,'../../language_reference.json'),'utf8'));
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'repeated-'+name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,TextEncoder,URL,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,async hover(target,focus=false){assert(target);const selection=JSON.stringify(reader.getSelection());if(focus)await target.trigger('focus');else{dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}for(let round=0;round<3;round++)for(const [id,fn]of [...timers])if(timers.has(id)){timers.delete(id);fn();}assert.equal(JSON.stringify(reader.getSelection()),selection);const tip=root.querySelector('.lr-proof-symbol:not([hidden])')||root.querySelector('.lr-token-help');assert(tip,target.textContent);return tip;},done(){assert.equal(JSON.stringify(bundle),before,'source, declarations and proof identities remain unchanged');reader.destroy();}};
}
function atSourcePosition(row,offset){
 for(const node of row.querySelector('.lr-source-code').childNodes){const length=node.textContent.length;if(offset<length)return node;offset-=length;}
 assert.fail('source position was not rendered');
}
async function run(){
 let checks=0;
 const cases=[['sets','{1} $in {{1}, {2}}','{1}','obj:list_set','{'],['fields-calls','p.point.x = p.point.x','p.point.x','obj:field','.'],['fields-calls','o.f(2) = o.f(2)','o.f(2)','obj:call','(']];
 for(const locale of ['zh','en'])for(const [name,lineText,expression,key,anchor] of cases){
  const bundle=fixture(name);assert.equal(bundle.run_result,'success');const source=bundle.sources.find(s=>s.id===bundle.entry_source_id),lines=source.content.split('\n'),line=lines.findIndex(text=>text.trim()===lineText)+1;assert(line);
  const lineStart=lines.slice(0,line-1).join('\n').length+(line>1?1:0),lineEnd=lineStart+lines[line-1].length,encoder=new TextEncoder(),startByte=encoder.encode(source.content.slice(0,lineStart)).length,endByte=encoder.encode(source.content.slice(0,lineEnd)).length;
  const hints=bundle.statements.filter(s=>s.source_id===source.id).flatMap(s=>s.expression_hints||[]).filter(h=>h.reference_key===key&&h.source_text===expression&&h.start_byte>=startByte&&h.end_byte<=endByte);assert.equal(hints.length,2,name);assert.notEqual(hints[0].start_byte,hints[1].start_byte);
  const view=mount(bundle,locale),row=view.root.querySelector('[data-line="'+line+'"]');
  for(const hint of hints){
   const bytes=new TextEncoder().encode(source.content);assert.equal(new TextDecoder().decode(bytes.slice(hint.start_byte,hint.end_byte)),expression);
   const start=new TextDecoder().decode(bytes.slice(0,hint.start_byte)).length-lineStart,token=atSourcePosition(row,start+expression.indexOf(anchor));assert.equal(token.dataset.expressionReference,key);
   for(const focus of [false,true]){const tip=await view.hover(token,focus);assert(tip.textContent.includes(catalogue.entries[key].summary[locale]));assert(tip.textContent.includes(catalogue.entries[key].notes[locale]));checks++;}
  }
  const equal=row.querySelector('.lr-chain-equality');if(equal)assert(!equal.dataset.expressionReference,'individual equality proofs retain priority');view.done();
 }
 for(const locale of ['zh','en']){
  const bundle=fixture('body-braces'),view=mount(bundle,locale);assert.equal(bundle.run_result,'success');assert.equal(view.root.querySelectorAll('[data-expression-reference="obj:list_set"]').length,0,'a function body and a list set cannot share the set explanation');assert(view.root.querySelector('[data-expression-reference="obj:anonymous_fn"]'));
  const input=view.root.querySelector('.lr-ide-input');input.value+='\n';await input.trigger('input');assert.equal(view.root.querySelectorAll('[data-expression-reference]').length,0);view.done();
 }
 console.log(JSON.stringify({passed:true,bilingualRepeatedHoverFocus:checks,bothOccurrences:true,fieldAndCallPriority:true,mixedFunctionBodyBracesOmitted:true,sourceAndEvidenceUnchanged:true,editInvalidation:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
