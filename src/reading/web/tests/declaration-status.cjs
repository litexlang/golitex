'use strict';
// Declaration verdicts, through public source hover, selection and navigation.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node declaration-status.cjs <declaration-status-fixtures>');
const code=fs.readFileSync(process.env.LITEX_READER_JS||path.join(__dirname,'../reader.js'),'utf8');
const read=name=>JSON.parse(fs.readFileSync(path.join(directory,name),'utf8'));
function mount(bundle,locale,editable){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 return {...dom,root,reader,token(id,line){return root.querySelectorAll('.lr-source-code [data-symbol]').find(n=>n.dataset.symbol===id&&(!line||n.closest('.lr-code-row').dataset.line===String(line)));},async hover(token,keyboard=false){
  assert(token);if(keyboard)token.focus();else if(editable){dom.document.elementFromPoint=()=>token;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else {await token.trigger('mouseenter');await token.trigger('pointermove');}
  for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}
  return root.querySelector('.lr-proof-symbol')||root.querySelector('.lr-token-help');
 },async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(bundle),before,'presentation preserves original source, identities, scopes and evidence');reader.destroy();}};
}
function declaration(bundle,name){const symbol=bundle.symbols.find(s=>s.name===name);assert(symbol,name);return {symbol,statement:bundle.statements.find(s=>s.declaration_symbol_ids?.includes(symbol.id))};}
const failedCases=[
 ['declaration-failed-objects.json','a'],
 ['declaration-failed-function-domain.json','f'],
 ['declaration-failed-function-body.json','f'],
 ['declaration-failed-theorem.json','bad'],
 ['declaration-failed-strategy.json','bad']
];
async function rejected(bundle,name,locale,editable){
 const {symbol,statement}=declaration(bundle,name);assert.equal(statement.status,'rejected');const v=mount(bundle,locale,editable),token=v.token(symbol.id,statement.line),help=await v.hover(token);
 assert(help);const notice=help.querySelector('.lr-declaration-status');assert(notice,'rejected symbol hover must not claim a completed definition');assert.equal(notice.dataset.status,'rejected');assert(help.querySelector('.lr-definition-source'));assert(!help.querySelector('.lr-symbol-domain,.lr-predicate-definition,.lr-introduction-properties'));
 await v.close();await v.token(symbol.id,statement.line).click();assert.equal(v.reader.getSelection().symbol,symbol.id);const body=v.root.querySelector('.lr-detail-body');assert(body.querySelector('.lr-declaration-status'));assert(!body.querySelector('.lr-symbol-domain,.lr-introduction-properties,.lr-formula'),'attempted declarations do not assert defining equations or membership');
 const link=body.querySelector('.lr-declaration-check-link');assert(link);await link.click();assert.equal(v.reader.getSelection().statement,statement.id);assert.equal(v.reader.getSelection().symbol,null);assert(v.root.querySelector('.lr-detail-body').textContent.length>0);await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().symbol,symbol.id);assert(v.root.querySelector('.lr-detail-body .lr-declaration-status'));
 await v.close();const keyboard=await v.hover(v.token(symbol.id,statement.line),true);assert(keyboard?.querySelector('.lr-declaration-status'));
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-token-help,.lr-proof-popover'));}
 v.done();
}
(async()=>{
 let checked=0;
 for(const locale of ['zh','en'])for(const editable of [true,false]){
  for(const[file,name]of failedCases){await rejected(read(file),name,locale,editable);checked++;}
  const b=read('declaration-completed-objects.json'),{symbol,statement}=declaration(b,'a'),v=mount(b,locale,editable),help=await v.hover(v.token(symbol.id,statement.line));assert(!help.querySelector('.lr-declaration-status'));await v.close();await v.token(symbol.id,statement.line).click();assert(v.root.querySelector('.lr-detail-body .lr-formula'));assert(!v.root.querySelector('.lr-detail-body .lr-declaration-status'));v.done();checked++;
  // A valid definition remains valid when the calling instance is rejected.
  const caller=read('declaration-failed-caller.json'),pred=caller.symbols.find(s=>s.kind==='DefPropStmt'),cv=mount(caller,locale,editable),use=caller.occurrences.find(o=>o.symbol_id===pred.id&&!o.definition),line=caller.statements.find(s=>s.id===use.statement_id).line,ph=await cv.hover(cv.token(pred.id,line));assert(!ph.querySelector('.lr-declaration-status'));assert(ph.querySelector('.lr-predicate-definition'));await cv.close();await cv.token(pred.id,line).click();assert(cv.root.querySelector('.lr-detail-body .lr-formula'));assert(!cv.root.querySelector('.lr-detail-body .lr-declaration-status'));cv.done();checked++;
  // A local declaration commits in its own scope even if its parent later fails.
  const local=read('declaration-local-in-failed-proof.json'),ld=declaration(local,'temporary'),lv=mount(local,locale,editable),lh=await lv.hover(lv.token(ld.symbol.id,ld.statement.line));assert(lh.querySelector('.lr-local-definition'));assert(!lh.querySelector('.lr-declaration-status'));assert(lh.querySelector('.lr-proof-context'));await lv.close();await lv.token(ld.symbol.id,ld.statement.line).click();assert(lv.root.querySelector('.lr-detail-body .lr-local-definition'));assert(lv.root.querySelector('.lr-detail-body .lr-formula'));assert(!lv.root.querySelector('.lr-detail-body .lr-declaration-status'));lv.done();checked++;
  // Formal parameters are not failed global declarations of their parent.
  const formal=read('declaration-failed-function-domain.json'),fv=mount(formal,locale,editable),x=formal.symbols.find(s=>s.name==='x'),fh=await fv.hover(fv.token(x.id));assert(!fh.querySelector('.lr-declaration-status'));assert(fh.querySelector('.lr-definition-source'));fv.done();checked++;
  const repeated=read('declaration-repeated.json'),rd=declaration(repeated,'a'),executions=repeated.statements.filter(s=>s.declaration_symbol_ids?.includes(rd.symbol.id));assert.equal(executions.length,2);
  for(const execution of executions){const rv=mount(repeated,locale,editable);await rv.reader.selectStatement(execution.id);const rh=await rv.hover(rv.token(rd.symbol.id,execution.line));assert(!rh.querySelector('.lr-declaration-status'));assert(rh.querySelector('.lr-local-definition'));await rv.close();await rv.token(rd.symbol.id,execution.line).click();assert.equal(rv.reader.getSelection().statement,execution.id);await rv.root.querySelector('.lr-detail-body .lr-introduction-link').click();assert.equal(rv.reader.getSelection().statement,execution.id,'definition checks retain the selected execution');rv.done();checked++;}
  // Synthetic transport controls: missing verdicts cannot establish properties.
  for(const control of ['missing','not_exported','future']){
   const incomplete=read('declaration-completed-objects.json'),d=declaration(incomplete,'a');if(control==='missing')delete d.statement.status;else d.statement.status=control;
   const iv=mount(incomplete,locale,editable),ih=await iv.hover(iv.token(d.symbol.id,d.statement.line));assert.equal(ih.querySelector('.lr-declaration-status').dataset.status,'incomplete');assert(!ih.querySelector('.lr-symbol-domain,.lr-introduction-properties'));await iv.close();await iv.token(d.symbol.id,d.statement.line).click();assert.equal(iv.root.querySelector('.lr-detail-body .lr-declaration-status').dataset.status,'incomplete');assert(!iv.root.querySelector('.lr-detail-body .lr-formula,.lr-introduction-properties'));iv.done();checked++;
  }
  // A conflicting use scope must not borrow either induction execution.
  const ambiguous=read('declaration-repeated.json'),ad=declaration(ambiguous,'a'),useStmt=ambiguous.statements.find(s=>s.id==='statement3');useStmt.scope_id='foreign';const av=mount(ambiguous,locale,editable);await av.reader.selectStatement(useStmt.id);const ah=await av.hover(av.token(ad.symbol.id,useStmt.line));assert.equal(ah.querySelector('.lr-declaration-status').dataset.status,'incomplete');assert(!ah.querySelector('.lr-introduction-properties'));await av.close();await av.token(ad.symbol.id,useStmt.line).click();assert.equal(av.root.querySelector('.lr-detail-body .lr-declaration-status').dataset.status,'incomplete');assert.equal(av.root.querySelectorAll('.lr-detail-body .lr-declaration-check-link').length,2);assert(!av.root.querySelector('.lr-detail-body .lr-formula'));av.done();checked++;
 }
 console.log(JSON.stringify({passed:true,checked,bilingualEditableAndReadOnly:true,hoverAndClick:true,failedCallerKeepsDefinition:true,acceptedLocalInRejectedParent:true,formalParametersSeparate:true,repeatedExecutionsAndAmbiguity:true,missingVerdictNotAccepted:true,exactBackAndKeyboard:true,sourceAndNativeUnchanged:true,browserObserved:false}));
})().catch(error=>{console.error(error);process.exitCode=1;});
