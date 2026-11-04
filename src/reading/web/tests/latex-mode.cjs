'use strict';
// Public shared-reader events with actual CLI bundles. This fixture models no
// browser geometry. The real local KaTeX engine checks every displayed formula.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),compiler=process.argv[2]==='--compiler'?path.resolve(process.argv[3]):null,directory=compiler?null:process.argv[2];
if(!directory&&!compiler)throw new Error('Usage: node latex-mode.cjs <native-fixtures> | --compiler <release-litex>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),katex=require('../vendor/katex/katex.min.js');
function fixture(name){
 if(!compiler)return JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8'));
 const type=name.startsWith('type-'),[kind,locale]=type?['type','en']:name.split('-');
 let input;
 if(type)input=['-f',path.resolve(__dirname,'../../../../examples/test_statements',name.slice(5)+'.lit')];
 else if(kind==='proof')input=['-f',path.resolve(__dirname,'../../../../examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit')];
 else input=['-e',kind==='duplicate'?'claim:\n    ? 1=1\n    1=1\n1=1\n':'1=1\n1=2\nhave\n3=3\n'];
 const result=require('node:child_process').spawnSync(compiler,['-reading','-latex',...(type?[]:['-strict']),'-json','-lang',locale,...input],{encoding:'utf8',maxBuffer:16*1024*1024});
 if(type)assert([0,1].includes(result.status),result.stderr);else assert.equal(result.status,kind==='failed'?1:0,result.stderr);return JSON.parse(result.stdout);
}
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
 const files=directory?fs.readdirSync(directory).filter(name=>name.startsWith('type-')&&name.endsWith('.json')):fs.readdirSync(path.resolve(__dirname,'../../../../examples/test_statements')).filter(name=>name.endsWith('.lit')).map(name=>'type-'+name.slice(0,-4)+'.json');
 for(const file of files){
  const bundle=fixture(file.slice(0,-5)),view=mount(bundle);
  assert(view.root.querySelector('.lr-manuscript'),file+': '+view.root.textContent);
  assert.equal(view.root.querySelectorAll('.lr-code-row').length,0,file+' must use native mathematical layout');
  assert(view.formulas>0,file);formulas+=view.formulas;view.done();checked++;
 }
 assert.equal(checked,52);
 for(const locale of ['en','zh'])for(const editable of [false,true]){
  const bundle=fixture('proof-'+locale),view=mount(bundle,locale,editable);
  assert(!view.root.querySelector('.lr-tex-description'));assert(!view.root.querySelector('.lr-tex-quote'));
  const proofParagraphs=view.root.querySelectorAll('.lr-tex-paragraph').filter(node=>node.textContent.includes(locale==='zh'?'证明.':'Proof.'));
  assert.equal(proofParagraphs.length,1,'one proof paragraph');
  for(const retained of locale==='zh'?['情形 1.','情形 2.','反证法.','反设','又有','综上']:['Case 1.','Case 2.','Proof by contradiction.','For contradiction','We also have','In all cases'])assert(proofParagraphs[0].textContent.includes(retained),retained+' stays in the same paragraph');
  assert(!view.root.querySelector('.lr-ide-input'),'mathematical mode initially shows the manuscript');
  const joined=view.root.querySelectorAll('.lr-tex-paragraph').some(node=>node.textContent.replace(/\s+/g,'').includes(locale==='zh'?'假设n=1，则n=1\\lorn>1。':'Supposen=1.Thenn=1\\lorn>1.'));
  assert(joined,'the case assumption and its first conclusion form one readable paragraph');
  const prose=view.root.querySelector('.lr-manuscript').textContent;
  assert(prose.includes(locale==='zh'?'综上':'In all cases'));assert(prose.includes(locale==='zh'?'因此':'so n > 1'));
  const transitionStatement=bundle.statements.find(record=>record.statement_kind==='Fact'&&record.source_text.trim()==='n = 1 or n > 1');
  const then=view.root.querySelectorAll('[data-latex-statement]').find(node=>node.dataset.latexStatement===transitionStatement.id&&node.textContent.trim()===(locale==='zh'?'则':'Then'));
  assert(then,'the transition word has compiler-owned statement identity');
  const transitionCard=await view.hover(then);
  assert(transitionCard.querySelector('.lr-formal-source pre').textContent.includes(transitionStatement.source_text.trim()),'new connective points to the exact original statement');
  await view.root.trigger('keydown',{key:'Escape'});
  const statement=bundle.statements.find(record=>record.source_text.trim()==='n <= 1'),control=view.root.querySelectorAll('[data-latex-statement]').find(node=>node.dataset.latexStatement===statement.id&&node.getAttribute('aria-label')==='n \\leq 1');
  assert(control,'a proof step has its own compiler identity');let card=await view.hover(control);assert(card);assert(card.querySelector('.lr-formal-source pre').textContent.includes('n <= 1'));
  assert(!view.reader.getSelection().explanationOpen,'hover does not change the selected statement or open a standing panel');
  await control.click();card=view.root.querySelector('.lr-proof-popover');await control.trigger('pointerleave');assert(view.root.querySelector('.lr-proof-popover'),'click pins the popup');
  const link=card.querySelector('.lr-fact-link');assert(link,'the shared proof component retains real fact references');
  const fact=link.dataset.fact;await link.click();assert.equal(view.reader.getSelection().fact,fact);
  assert(view.root.querySelector('.lr-manuscript'),'fact navigation keeps mathematical presentation');
  await view.root.trigger('keydown',{key:'Escape'});
  const lower=bundle.statements.find(record=>record.source_text.trim()==='n >= 1'),lowerId=lower.mathematics.subject_fact_id;
  let reason=view.root.querySelectorAll('.lr-math-reason').find(node=>node.dataset.statement===lower.id);
  assert(reason,'a checked primary fact has an inline derivation');assert.equal(reason.dataset.fact,lowerId);
  assert(!reason.open);assert(!reason.querySelector('.lr-math-reason-body'),'closed derivations render lazily');
  await reason.querySelector('summary').click();assert(reason.open);
  const bound=reason.querySelector('.lr-positive-natural-bound');assert.equal(bound.dataset.status,'verified');
  assert(bound.querySelector('.lr-premise-conclusion').textContent.includes(locale==='zh'?'推出':'we obtain'));
  assert(bound.querySelector('.lr-premise-conclusion').textContent.includes(locale==='zh'?'正自然数至少为 1':'positive natural number is at least 1'));
  assert(bound.textContent.includes('n ≥ 1'));assert(!reason.querySelector('.lr-atomic-wd').open,'formation checks remain independently collapsed');
  const premise=bound.querySelector('.lr-proof-step');assert(!premise.open);await premise.querySelector('summary').click();
  const premiseLink=premise.querySelector('.lr-fact-link');assert(premiseLink,'the actual membership premise remains traceable');
  assert(lower.cited_fact_ids.includes(premiseLink.dataset.fact),'the source declaration is a native citation');
  const body=reason.querySelector('.lr-math-reason-body');await reason.querySelector('summary').click();assert(!reason.open);await reason.querySelector('summary').click();assert(reason.open);assert.equal(reason.querySelector('.lr-math-reason-body'),body,'reopening reuses the same rendered proof');
  await reason.querySelector('.lr-math-reason-source').click();assert(view.root.querySelector('.lr-proof-popover .lr-formal-source pre').textContent.includes(lower.source_text));await view.root.trigger('keydown',{key:'Escape'});
  assert.equal(reason.querySelector('.lr-math-reason-source').getAttribute('aria-haspopup'),'dialog');assert.notEqual(reason.querySelector('.lr-math-reason-source').getAttribute('aria-expanded'),'true','a closed source dialog must not leave a stale expansion state');
  const premiseId=premiseLink.dataset.fact;await premiseLink.click();assert.equal(view.reader.getSelection().fact,premiseId);await view.root.trigger('keydown',{key:'Escape'});
  const sourceButton=view.root.querySelector('[data-layout="source"]');await sourceButton.click();assert(view.root.querySelector('.lr-code-row'));
  if(editable){const input=view.root.querySelector('.lr-ide-input');assert(input);input.value+=' ';await input.trigger('input');const mathButton=view.root.querySelector('[data-layout="latex"]');assert(mathButton.disabled,'an edited source cannot reuse stale mathematical evidence');}
  else {await view.root.querySelector('[data-layout="latex"]').click();assert(view.root.querySelector('.lr-manuscript'));}
  view.done();
 }
 const duplicate=fixture('duplicate-en'),dv=mount(duplicate),facts=duplicate.statements.filter(s=>s.statement_kind==='Fact');assert.equal(facts.length,2);
 for(const statement of facts){const control=dv.root.querySelectorAll('[data-latex-statement]').find(n=>n.dataset.latexStatement===statement.id);assert(control);const card=await dv.hover(control);assert(card.querySelector('.lr-formal-source pre').textContent.includes('1=1'));await dv.root.trigger('keydown',{key:'Escape'});}dv.done();
 const failed=fixture('failed-en'),fv=mount(failed);assert(fv.root.querySelector('.lr-latex-rejected'));assert(fv.root.querySelector('.lr-latex-original').textContent.includes('3=3'));assert(!fv.root.querySelector('.lr-manuscript').textContent.includes('3 = 3'));fv.done();
 for(const kind of ['missing','result','goal','bound','member','set','rule','producer','scope','role','status','ambiguous']){
  const bundle=fixture('proof-en'),statement=bundle.statements.find(s=>s.source_text.trim()==='n >= 1'),fact=bundle.facts.find(f=>f.id===statement.mathematics.subject_fact_id),nodes=new Map(bundle.evidence_nodes.map(row=>[row.id,row.node]));
  function resolve(value){const seen=new Set();while(value?.kind==='evidence_reference'&&!seen.has(value.evidence_id)){seen.add(value.evidence_id);value=nodes.get(value.evidence_id);}return value;}
  function result(value){let node=resolve(value);while(node?.fields?.['0']&&!node.fields.searched_proof)node=resolve(node.fields['0']);return node;}
  const proof=result(fact.evidence),goal=result(proof.fields.fact);let rule=resolve(proof.fields.searched_proof);while(rule?.type!=='GreaterEqualFactSearchProofByBuiltinRule')rule=resolve(rule.fields['0']);
  const premise=result(resolve(rule.fields['0']).fields.premise_proof),membership=result(premise.fields.fact);
  if(kind==='missing')delete fact.evidence;
  if(kind==='result')proof.type='VerifyAtomicExceptEqualityFactFailed';
  if(kind==='goal')goal.fields.fact_id={kind:'fact_identity',fact_id:'foreign'};
  if(kind==='bound')result(goal.fields.right).fields.normalized_value='2';
  if(kind==='member')membership.fields.element=goal.fields.right;
  if(kind==='set')resolve(resolve(membership.fields.set).fields['0']).symbol_id='builtin:set:N';
  if(kind==='rule')rule.rule_id='foreign';
  if(kind==='producer')fact.producer_statement_id='foreign';
  if(kind==='scope')fact.scope_id='foreign';
  if(kind==='role')fact.role='hypothesis';
  if(kind==='status')statement.status='rejected';
  if(kind==='ambiguous')bundle.statements.push({...statement,id:'repeated-execution',source_statement_id:statement.id});
  const view=mount(bundle),reason=view.root.querySelectorAll('.lr-math-reason').find(node=>node.dataset.statement===statement.id);
  if(['producer','scope','role','status','ambiguous'].includes(kind))assert(!reason,kind+' must not borrow an inline proof');
  else{assert(reason);await reason.querySelector('summary').click();assert(!reason.querySelector('.lr-positive-natural-bound[data-status="verified"]'),kind+' must not fabricate a derivation');assert(reason.querySelector('.lr-empty-note'));}
  view.done();
 }
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
 console.log(JSON.stringify({passed:true,nativeStatementFixtures:checked,checkedFormulas:formulas,liveCompiler:!!compiler,fluentProofProse:true,bilingualHoverSourceAndProof:true,pinCitationAndSourceSwitch:true,collapsibleNativeDerivations:true,derivationCorruptionControls:12,unchangedEvidence:true,malformedMappingsAndStaleEditsRejected:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
