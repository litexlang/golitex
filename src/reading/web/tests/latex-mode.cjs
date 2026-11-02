'use strict';
// Public shared-reader events with actual CLI bundles. This fixture models no
// browser geometry. The real local KaTeX engine checks every displayed formula.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node latex-mode.cjs <native-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),katex=require('../vendor/katex/katex.min.js');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8'));
function mount(bundle,locale='en',editable=false,renderer=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0,formulas=0;
 if(renderer)dom.window.katex={render(tex,node,options){katex.renderToString(tex,options);node.textContent=tex;formulas++;}};
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 return {...dom,root,reader,get formulas(){return formulas;},async hover(control){await control.trigger('pointerenter');for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},
  done(){assert.equal(JSON.stringify(bundle),before,'presentation must preserve native source/evidence records');reader.destroy();}};
}
async function run(){
 let checked=0,formulas=0;
 for(const file of fs.readdirSync(directory).filter(name=>name.startsWith('type-')&&name.endsWith('.json'))){
  const bundle=fixture(file.slice(0,-5)),view=mount(bundle);
  assert(view.root.querySelector('.lr-manuscript'),file+': '+view.root.textContent);
  assert.equal(view.root.querySelectorAll('.lr-code-row').length,0,file+' must use native mathematical layout');
  assert(view.formulas>0,file);formulas+=view.formulas;view.done();checked++;
 }
 assert.equal(checked,52);
 for(const locale of ['en','zh'])for(const editable of [false,true]){
  const bundle=fixture('proof-'+locale),view=mount(bundle,locale,editable);
  assert(view.root.querySelector('.lr-tex-description'));assert(view.root.querySelector('.lr-tex-quote'));
  assert(!view.root.querySelector('.lr-ide-input'),'mathematical mode initially shows the manuscript');
  const statement=bundle.statements.find(record=>record.source_text.trim()==='n <= 1'),control=view.root.querySelectorAll('[data-latex-statement]').find(node=>node.dataset.latexStatement===statement.id&&node.getAttribute('aria-label')==='n \\leq 1');
  assert(control,'a proof step has its own compiler identity');let card=await view.hover(control);assert(card);assert(card.querySelector('.lr-formal-source pre').textContent.includes('n <= 1'));
  assert(!view.reader.getSelection().explanationOpen,'hover does not change the selected statement or open a standing panel');
  await control.click();card=view.root.querySelector('.lr-proof-popover');await control.trigger('pointerleave');assert(view.root.querySelector('.lr-proof-popover'),'click pins the popup');
  const link=card.querySelector('.lr-fact-link');assert(link,'the shared proof component retains real fact references');
  const fact=link.dataset.fact;await link.click();assert.equal(view.reader.getSelection().fact,fact);
  assert(view.root.querySelector('.lr-manuscript'),'fact navigation keeps mathematical presentation');
  await view.root.trigger('keydown',{key:'Escape'});
  const sourceButton=view.root.querySelector('[data-layout="source"]');await sourceButton.click();assert(view.root.querySelector('.lr-code-row'));
  if(editable){const input=view.root.querySelector('.lr-ide-input');assert(input);input.value+=' ';await input.trigger('input');const mathButton=view.root.querySelector('[data-layout="latex"]');assert(mathButton.disabled,'an edited source cannot reuse stale mathematical evidence');}
  else {await view.root.querySelector('[data-layout="latex"]').click();assert(view.root.querySelector('.lr-manuscript'));}
  view.done();
 }
 const duplicate=fixture('duplicate-en'),dv=mount(duplicate),facts=duplicate.statements.filter(s=>s.statement_kind==='Fact');assert.equal(facts.length,2);
 for(const statement of facts){const control=dv.root.querySelectorAll('[data-latex-statement]').find(n=>n.dataset.latexStatement===statement.id);assert(control);const card=await dv.hover(control);assert(card.querySelector('.lr-formal-source pre').textContent.includes('1=1'));await dv.root.trigger('keydown',{key:'Escape'});}dv.done();
 const failed=fixture('failed-en'),fv=mount(failed);assert(fv.root.querySelector('.lr-latex-rejected'));assert(fv.root.querySelector('.lr-latex-original').textContent.includes('3=3'));assert(!fv.root.querySelector('.lr-manuscript').textContent.includes('3 = 3'));fv.done();
 for(const kind of ['snapshot','identity','source','range','parent','missing','renderer']){
  const bundle=fixture('proof-en'),source=bundle.sources[0],block=source.latex_blocks[0];
  if(kind==='snapshot')source.content+=' changed';
  if(kind==='identity')block.statements[0].statement_id='missing';
  if(kind==='source')bundle.statements[0].source_id='foreign';
  if(kind==='range')block.statements[0].end_byte=10000000;
  if(kind==='parent')bundle.statements[1].parent_statement_id='foreign';
  if(kind==='missing')delete source.latex_blocks;
  // A suffix change outside a block is still an uncovered original source;
  // replace bytes inside the mapped block to test snapshot invalidation.
  if(kind==='snapshot')source.content=source.content.replace('n >= 1','n >= 9');
  const view=mount(bundle,'en',false,kind!=='renderer');
  assert(!view.root.querySelector('.lr-manuscript'),kind+' must fall back to original source');assert(view.root.querySelector('.lr-code-row'));view.done();
 }
 console.log(JSON.stringify({passed:true,nativeStatementFixtures:checked,checkedFormulas:formulas,bilingualHoverSourceAndProof:true,pinCitationAndSourceSwitch:true,unchangedEvidence:true,malformedMappingsAndStaleEditsRejected:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
