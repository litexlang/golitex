'use strict';
// Actual Native static parts, public open/navigation/snapshot APIs, no network.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),katex=require('../vendor/katex/katex.min.js'),directory=path.resolve(process.argv[2]||'');
if(!process.argv[2])throw new Error('Usage: node latex-lazy.cjs <native-mathematical-book-export>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),full=JSON.parse(fs.readFileSync(path.join(directory,'reading.json'),'utf8'));
assert.equal(fs.readFileSync(path.join(directory,'reader.js'),'utf8'),code,'the native export embeds the current shared reader');
assert.equal(fs.readFileSync(path.join(directory,'reader.css'),'utf8'),fs.readFileSync(path.join(__dirname,'../reader.css'),'utf8'));
async function open(locale,layout='latex'){
 const data=JSON.parse(fs.readFileSync(path.join(directory,'reading.manifest.json'),'utf8')),before=JSON.stringify(data),dom=createDOM(),root=dom.root(),requests=[],timers=new Map();let serial=0;
 dom.window.katex={render(tex,node,options){katex.renderToString(tex,options);node.textContent=tex;}};
 const fetch=async address=>{const url=new URL(address);assert.equal(url.origin,'https://reading.test');const file=path.resolve(directory,decodeURIComponent(url.pathname.slice(1)));assert(file.startsWith(directory+path.sep));requests.push(path.relative(directory,file));return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
 vm.runInContext(code,vm.createContext({...dom,fetch,URL,TextEncoder,Map,Set,console,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout:id=>timers.delete(id)}));
 const reader=await dom.window.LitexReading.open(root,data,{baseUrl:'https://reading.test/reading.manifest.json',locale,layout,onCheck:async()=>full});
 return {...dom,root,reader,requests,async hover(control){await control.trigger('pointerenter');for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},done(){assert.equal(JSON.stringify(data),before,'loading/navigation never mutates the Native manifest');reader.destroy();}};
}
async function main(){
 assert.equal(full.reading_layout,'latex');assert.equal(full.run_result,'success');assert(full.sources.length>=3);let checked=0;
 for(const locale of ['en','zh']){
  const view=await open(locale);assert.equal(view.requests.length,1,'initial reading loads one proof chapter');assert(view.root.querySelector('.lr-manuscript'));
  for(const source of full.sources){
   const statement=full.statements.find(s=>s.source_id===source.id&&s.status==='accepted'&&(s.source_statement_id||s.id)===s.id);assert(statement);await view.reader.selectStatement(statement.id);
   assert.equal(view.reader.getSelection().source,source.id);assert(view.root.querySelector('.lr-manuscript'));assert(view.root.querySelector('.lr-context-explanation'));
   await view.root.trigger('keydown',{key:'Escape'});const control=view.root.querySelectorAll('[data-latex-statement]').find(n=>n.dataset.latexStatement===statement.id),card=await view.hover(control);assert(card.querySelector('.lr-proof-evidence'));assert(!card.querySelector('.lr-math-source').open);
   assert.equal(card.querySelector('.lr-formal-source pre').textContent,Buffer.from(source.content).subarray(statement.start_byte,statement.end_byte).toString().trimEnd());
   const symbols=card.querySelector('.lr-math-symbols');if(symbols){await symbols.querySelector('summary').click();const token=symbols.querySelector('.lr-math-symbol');await token.click();assert(!card.querySelector('.lr-proof-symbol').hidden);}
   await view.root.trigger('keydown',{key:'Escape'});checked++;
  }
  const snapshot=await view.reader.getProjectSnapshot();assert.deepEqual(Array.from(snapshot.sources,s=>s.content),full.sources.map(s=>s.content));assert.equal(view.reader.getReadingLayout(),'latex');view.done();
  // The same mathematical bundle can still use the public source-layout
  // override, navigate lazy chapters and retain its original working source.
  const source=await open(locale,'source');assert(source.root.querySelector('.lr-ide-input'));
  const destination=full.statements.find(s=>s.source_id===full.sources.at(-1).id);await source.reader.selectStatement(destination.id);assert.equal(source.root.querySelector('.lr-ide-input').value,full.sources.at(-1).content);source.done();
 }
 console.log(JSON.stringify({passed:true,nativeLazyChapters:checked,currentEmbeddedAssets:true,bilingualMathProofAndSymbols:true,exactSourceAndSnapshot:true,sourceOverride:true,nativeManifestUnchanged:true,browserGeometry:false}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
