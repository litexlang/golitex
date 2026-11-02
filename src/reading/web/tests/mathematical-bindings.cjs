'use strict';
// Real native binders through public source events; altered payloads are controls only.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node mathematical-bindings.cjs <foundation-fixtures> [native-export]');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'foundation-eval-'+name+'.json'),'utf8'));
function records(bundle){
 const nodes=new Map(bundle.evidence_nodes.map(row=>[row.id,row.node]));
 function resolve(value){const seen=new Set();while(value?.kind==='evidence_reference'&&!seen.has(value.evidence_id)){seen.add(value.evidence_id);value=nodes.get(value.evidence_id);}return value||{};}
 function visit(value,fn,seen=new Set()){if(!value||typeof value!=='object'||seen.has(value))return;seen.add(value);fn(value);if(value.kind==='evidence_reference')visit(nodes.get(value.evidence_id),fn,seen);else for(const child of Object.values(value))visit(child,fn,seen);}
 return {nodes,resolve,visit};
}
function mount(bundle,locale,editable=true){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
 const view={...dom,root,reader,async hover(statement){const row=root.querySelector('[data-line="'+statement.line+'"]');assert(row);await row.querySelector('.lr-line-number').trigger('focus');for(let i=0;i<3;i++)for(const [id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}const card=root.querySelector('.lr-proof-popover');assert(card);return card;},done(){assert.equal(JSON.stringify(bundle),before,'display preserves all native names, source, evidence and identities');reader.destroy();}};
 assert.equal(root.querySelectorAll('.lr-code-row').length,bundle.sources[0].content.split('\n').length);return view;
}
const statement=b=>b.statements.find(s=>s.status==='accepted'&&/Release(RegularityAxiom|AxiomOfChoice|ZornLemma)Stmt$/.test(s.statement_kind));
async function run(){
 let checked=0;const views=[];
 for(const locale of ['zh','en'])for(const editable of [true,false])for(const name of ['regularity','choice','zorn']){
  const b=fixture(name),v=mount(b,locale,editable),s=statement(b),card=await v.hover(s),part=card.querySelector('.lr-foundation-proof'),conclusion=part.querySelector('.lr-command-conclusion');assert(part);assert(!part.textContent.includes('__param_'),part.textContent);
  const wd=card.querySelector('.lr-atomic-wd');assert(wd&&!wd.open);assert.equal(wd.parentNode.children.at(-1),wd);
  if(name==='regularity'){
   assert(conclusion.textContent.includes('u ∈ {1}'));assert(conclusion.textContent.includes('intersect(u, {1}) = {}'));assert(conclusion.textContent.includes(locale==='zh'?'存在':'There exists'));
   const link=conclusion.querySelector('.lr-fact-link'),id=link.dataset.fact;await link.click();assert.equal(v.reader.getSelection().fact,id);assert(v.root.querySelector('.lr-detail-body').textContent.includes('intersect(u, {1}) = {}'));await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().focusLine,s.line);
  }else if(name==='choice'){
   assert(conclusion.textContent.includes('family_union(F)'));assert(conclusion.textContent.includes('is_choice_function_for(F, F,'));
   const binders=[...conclusion.textContent.matchAll(/fn \((\w+) F\)/g)].map(match=>match[1]);assert.equal(binders.length,2,conclusion.textContent);assert.notEqual(binders[0],binders[1],'co-occurring nested function binders retain distinct identities');
  }else{assert(card.textContent.includes('x, y, z ∈ S'),'source-authored parameter names stay unchanged');assert(conclusion.textContent.includes('maximal('));}
  // Opening actual premise certificates must use the same mathematical names.
  for(const detail of part.querySelectorAll('.lr-proof-step'))await detail.querySelector('summary').click();assert(!part.textContent.includes('__param_'),part.textContent);assert(!part.querySelector('.lr-proof-step .lr-origin-note'),'a verified premise does not inherit the foundation command’s axiom origin');assert(part.querySelector('.lr-foundation-origin'),'the actual foundation principle remains explicit');
  if(name==='zorn'){const pairs=part.querySelectorAll('.lr-quantifier-binding').map(node=>node.textContent);for(const text of ['x ↦ u','y ↦ v','z ↦ w'])assert(pairs.includes(text),text);assert(pairs.every(text=>text.includes(' ↦ ')&&!text.includes(' = ')),'alpha-renaming is not object equality');}
  if(editable){await v.root.trigger('keydown',{key:'Escape'});const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-proof-popover'));}
  views.push({name,locale,editable,text:part.textContent});v.done();checked++;
 }
 for(const control of ['missing-symbol','wrong-id','conflicting-id','conflicting-spelling','authored-binding','missing-binder','orphan-binder']){
  const b=fixture('regularity'),d=records(b),s=statement(b),symbol=b.symbols.find(s=>s.name==='__param_1');assert(symbol);const original=symbol.id;
  if(control==='missing-symbol')b.symbols=b.symbols.filter(s=>s!==symbol);
  if(control==='wrong-id'){symbol.id='local:i999';d.visit([...d.nodes.values()],n=>{if(n.kind==='symbol_reference'&&n.symbol_id===original)n.symbol_id=symbol.id;});}
  if(control==='conflicting-id'){const condition=[...d.nodes.values()].filter(n=>n.type==='EqualFact');let changed=false;d.visit(condition,n=>{if(!changed&&n.kind==='symbol_reference'&&n.symbol_id===original){n.symbol_id='local:i999';changed=true;}});assert(changed);}
  if(control==='conflicting-spelling'){let changed=false;d.visit([...d.nodes.values()],n=>{if(!changed&&n.kind==='symbol_reference'&&n.symbol_id===original){n.name='other_name';changed=true;}});assert(changed);}
  if(control==='authored-binding')b.occurrences.push({symbol_id:original,definition:true,source_id:s.source_id,statement_id:s.id,start_byte:0,end_byte:1,line:s.line});
  if(control==='missing-binder')for(const node of d.nodes.values())if(node.type==='TypedParameterGroup')node.fields.params=[];
  if(control==='orphan-binder')for(const node of d.nodes.values())if(node.type==='PlainExistFact')node.fields.typed_parameters={type:'TypedParameterList',fields:{groups:[]}};
  const v=mount(b,'en'),part=(await v.hover(s)).querySelector('.lr-command-conclusion');assert(part.textContent.includes('__param_1'),control+': uncertain identities must not receive guessed names');v.done();checked++;
 }
 // Synthetic collision control: rename the authored family consistently in a
 // native payload. This is display evidence, not a newly verified Litex proof.
 const collision=JSON.parse(JSON.stringify(fixture('choice')).replace(/\bF\b/g,'u')),cv=mount(collision,'en'),cp=(await cv.hover(statement(collision))).querySelector('.lr-command-conclusion');assert(cp.textContent.includes('family_union(u)'));assert(!cp.textContent.includes('(u u)'),'generated binders cannot capture the authored family');assert(!cp.textContent.includes('__param_'));cv.done();checked++;
 const unnamed=fixture('choice'),ud=records(unnamed);let unnamedCount=0;ud.visit([...ud.nodes.values()],node=>{if(node.kind==='symbol_reference'&&node.name==='F'){delete node.name;unnamedCount++;}});assert(unnamedCount);const uv=mount(unnamed,'en'),uc=(await uv.hover(statement(unnamed))).querySelector('.lr-command-conclusion');assert(uc.textContent.includes('__param_'),'an expression with unnamed peers cannot justify capture-free renaming');assert(!uc.textContent.includes('undefined'),'incomplete mathematical expressions use the retained fallback');uv.done();checked++;
 for(const locale of ['zh','en']){
  const b=fixture('zorn'),d=records(b),record=[...d.nodes.values()].find(node=>node.type==='VerifyKnownForallFactProof'&&node.fields.parameter_renamings.length===3&&String(b.symbols.find(s=>s.id==='local:'+d.resolve(node.fields.parameter_renamings[0]).fields.target.id)?.name).startsWith('__param_')),target=d.resolve(record.fields.fact).fields.fact_id.fact_id,source=record.fields.cite_fact_id.fact_id,v=mount(b,locale),card=await v.hover(statement(b));for(const detail of card.querySelectorAll('.lr-foundation-proof .lr-proof-step'))await detail.querySelector('summary').click();const alpha=card.querySelector('[data-target-fact="'+target+'"]');assert(alpha);const link=alpha.querySelector('.lr-fact-link');assert.equal(link.dataset.fact,source);await link.click();assert.equal(v.reader.getSelection().fact,source);await v.root.querySelector('.lr-back').click();assert(v.root.querySelector('.lr-detail-body .lr-foundation-proof'));v.done();checked++;
 }
 for(const control of ['missing-vector','wrong-source','wrong-target','reordered','duplicate','wrong-cite','missing-cite','missing-source-ast','missing-name','goal-identity-kind']){
  const b=fixture('zorn'),d=records(b),record=[...d.nodes.values()].find(node=>node.type==='VerifyKnownForallFactProof'&&node.fields.parameter_renamings.length===3&&String(b.symbols.find(s=>s.id==='local:'+d.resolve(node.fields.parameter_renamings[0]).fields.target.id)?.name).startsWith('__param_')),fields=record.fields,target=d.resolve(fields.fact).fields.fact_id.fact_id,cited=fields.cite_fact_id.fact_id,pairs=fields.parameter_renamings;
  if(control==='missing-vector')delete fields.parameter_renamings;if(control==='wrong-source')d.resolve(pairs[0]).fields.source={kind:'identifier_id',id:'i999999'};if(control==='wrong-target')d.resolve(pairs[0]).fields.target={kind:'identifier_id',id:'i999999'};if(control==='reordered')pairs.reverse();if(control==='duplicate')d.resolve(pairs[1]).fields.source=d.resolve(pairs[0]).fields.source;
  if(control==='wrong-cite'){const atomic=[...d.nodes.values()].find(n=>n.type==='IsNonemptySetFact'&&b.facts.some(f=>f.id===n.fields.fact_id?.fact_id));assert(atomic);fields.cite_fact_id={kind:'fact_reference',fact_id:atomic.fields.fact_id.fact_id};}if(control==='missing-cite')delete fields.cite_fact_id;
  if(control==='missing-source-ast')for(const node of d.nodes.values())if(node.type==='ForallFact'&&node.fields.fact_id?.fact_id===cited)delete node.fields.fact_id;
  if(control==='missing-name'){const source=[...d.nodes.values()].find(n=>n.type==='ForallFact'&&n.fields.fact_id?.fact_id===cited),group=d.resolve(d.resolve(source.fields.typed_parameters).fields.groups[0]);delete group.fields.params[0].name;}
  if(control==='goal-identity-kind')d.resolve(fields.fact).fields.fact_id.kind='fact_reference';
  const v=mount(b,'en'),card=await v.hover(statement(b));for(const detail of card.querySelectorAll('.lr-foundation-proof .lr-proof-step'))await detail.querySelector('summary').click();const alpha=card.querySelector('[data-target-fact="'+target+'"]');assert(alpha,control);assert(!alpha.querySelector('.lr-quantifier-binding'),control+': no guessed correspondence');assert(alpha.querySelector('.lr-empty-note'),control);v.done();checked++;
 }
 if(process.argv[3]){
  const exported=path.resolve(process.argv[3]);
  for(const locale of ['zh','en']){
   const manifest=JSON.parse(fs.readFileSync(path.join(exported,'reading.manifest.json'),'utf8')),whole=JSON.parse(fs.readFileSync(path.join(exported,'reading.json'),'utf8')),dom=createDOM(),root=dom.root(),reads=[];
   const fetch=async url=>{const u=new URL(url);assert.equal(u.origin,'https://reading.test');const file=path.resolve(exported,decodeURIComponent(u.pathname.slice(1)));assert(file.startsWith(exported+path.sep));reads.push(file);return {ok:true,json:async()=>JSON.parse(fs.readFileSync(file,'utf8'))};};
   vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,fetch,setTimeout,clearTimeout}));const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:'https://reading.test/reading.manifest.json',locale});
   const shown=[];
   for(const s of whole.statements.filter(s=>s.status==='accepted'&&/Release(RegularityAxiom|AxiomOfChoice|ZornLemma)Stmt$/.test(s.statement_kind))){await reader.selectStatement(s.id);const part=root.querySelector('.lr-detail-body .lr-foundation-proof');assert(part);assert(!part.textContent.includes('__param_'),part.textContent);shown.push({id:s.id,text:part.querySelector('.lr-command-conclusion').textContent});checked++;}
   for(const value of shown.reverse()){await reader.selectStatement(value.id);assert.equal(root.querySelector('.lr-detail-body .lr-command-conclusion').textContent,value.text,'loading another source must not change an already displayed binder name');checked++;}
   assert(reads.length>1);reader.destroy();
  }
 }
 console.log(JSON.stringify({passed:true,checked,bilingualEditableAndReadOnly:true,completeExistentialAndNestedDomains:true,actualIdentitiesAndAuthoredNamesPreserved:true,captureAndMalformedControls:true,navigationAndReturn:true,wdLastAndClosed:true,sourceRowsAndRecordsUnchanged:true,lazyNativeExport:!!process.argv[3],views}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
