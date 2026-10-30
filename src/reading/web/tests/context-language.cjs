'use strict';
// AST-owned source positions through the public component and real exports.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node context-language.cjs <context-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),catalogue=JSON.parse(fs.readFileSync(path.join(__dirname,'../../language_reference.json'),'utf8'));
const cases={
 'open-open':'obj:interval:open_open','open-closed':'obj:interval:open_closed',
 'closed-open':'obj:interval:closed_open','closed-closed':'obj:interval:closed_closed',
 'lower-open':'obj:ray:lower_open','lower-closed':'obj:ray:lower_closed',
 'upper-open':'obj:ray:upper_open','upper-closed':'obj:ray:upper_closed',
 'listed-set':'obj:list_set','set-builder':'obj:set_builder','anonymous':'obj:anonymous_fn',
 'function-space':'fn','structure':'obj:struct_type','field':'obj:field',
 'template':'obj:template','call':'obj:call'
};
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'context-'+name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,TextEncoder,URL,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 return {...dom,root,reader,async hover(target,focus=false){assert(target);const selection=JSON.stringify(reader.getSelection());if(focus)await target.trigger('focus');else{dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}for(let round=0;round<3;round++)for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);fn();}assert.equal(JSON.stringify(reader.getSelection()),selection);const tip=root.querySelector('.lr-proof-symbol:not([hidden])')||root.querySelector('.lr-token-help');assert(tip,target.textContent);return tip;},done(){assert.equal(JSON.stringify(bundle),before,'syntax hints never change proof or source records');reader.destroy();}};
}
async function run(){
 let accepted=0;
 for(const locale of ['zh','en'])for(const [name,key] of Object.entries(cases)){
  const bundle=fixture(name),view=mount(bundle,locale),token=view.root.querySelector('[data-expression-reference="'+key+'"]');assert(token,name+': '+key);assert(!token.dataset.keyword,'context punctuation does not become an ambiguous keyword selection');const tip=await view.hover(token),entry=catalogue.entries[key],card=entry.statement?catalogue.statements[entry.statement]:entry;assert(tip.textContent.includes(card.summary[locale]),tip.textContent);assert(tip.textContent.includes(card.notes[locale]),tip.textContent);const focused=await view.hover(token,true);assert(focused.textContent.includes(card.summary[locale]));assert.equal(view.root.querySelectorAll('.lr-json-pane,.lr-json-toggle').length,0);accepted++;view.done();
 }
 const call=fixture('call'),view=mount(call,'en'),symbol=view.root.querySelectorAll('[data-symbol]').find(token=>token.textContent==='reciprocal'&&token.closest('.lr-code-row').dataset.line==='2');assert(symbol);const info=await view.hover(symbol);assert(info.querySelector('.lr-definition-source'),'resolved symbols retain their declaration rather than generic application help');const eq=view.root.querySelector('.lr-code-row[data-line="2"] .lr-chain-equality');assert(eq&&!eq.dataset.expressionReference,'the exact equality proof keeps priority');await eq.click();assert.equal(view.reader.getSelection().chainStep,0);view.done();
 const guarded=mount(fixture('function-space'),'en'),comparison=guarded.root.querySelectorAll('[data-syntax]').find(token=>['<','>'].includes(token.textContent));assert(comparison);assert(!comparison.dataset.expressionReference,'comparisons inside a function guard are not template brackets');const comparisonHelp=await guarded.hover(comparison);assert(comparisonHelp.textContent.includes(catalogue.entries[comparison.textContent].summary.en));guarded.done();
 const shadow=mount(fixture('field-shadow'),'en'),row=shadow.root.querySelector('[data-line="5"]'),xs=row.querySelectorAll('[data-syntax]').filter(token=>token.textContent==='x');assert.equal(xs.length,4);assert.equal(xs.filter(token=>token.dataset.symbol).length,2);assert(!xs[0].dataset.symbol&&!xs[2].dataset.symbol,'field segments receive no variable identity');const variable=await shadow.hover(xs[1]);assert(variable.querySelector('.lr-symbol-domain').textContent.includes('R'));shadow.done();
 for(const control of ['missing','wrong-source','unknown-key','conflicting','invalid-byte','null']){
  const bundle=fixture('listed-set'),statement=bundle.statements.find(s=>s.expression_hints?.length),hint=statement.expression_hints[0];assert(hint);
  if(control==='missing')delete statement.expression_hints;
  if(control==='wrong-source')hint.source_text='a different expression';
  if(control==='unknown-key')hint.reference_key='obj:future';
  if(control==='conflicting')statement.expression_hints.push({...hint,reference_key:'obj:field'});
  if(control==='invalid-byte')hint.start_byte=1.5;
  if(control==='null')statement.expression_hints=[null];
  const v=mount(bundle,'en');assert.equal(v.root.querySelectorAll('[data-expression-reference]').length,0,control);v.done();
 }
 const edited=mount(fixture('listed-set'),'en'),token=edited.root.querySelector('[data-expression-reference]');await edited.hover(token);const input=edited.root.querySelector('.lr-ide-input');input.value+='\n';await input.trigger('input');assert(!edited.root.querySelector('.lr-proof-popover,.lr-token-help'));assert.equal(edited.root.querySelectorAll('[data-expression-reference]').length,0,'unchecked source gets no old expression map');edited.done();
 console.log(JSON.stringify({passed:true,bilingualContextCases:accepted,keyboardFocus:true,sourceBytesAndEvidenceUnchanged:true,symbolAndEqualityPriority:true,malformedAndLegacyFallback:true,editInvalidation:true,scope:'unique AST-owned source matches'}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
