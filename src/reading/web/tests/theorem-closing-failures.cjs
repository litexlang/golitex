'use strict';
// Actual caller-formation failures after completed local theorem checks.
const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),cp=require('node:child_process'),http=require('node:http'),vm=require('node:vm'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const {createDOM}=require('./dom.cjs'),options={binary:'target/release/litex',reader:path.join(__dirname,'../reader.js')};
for(let i=2;i<process.argv.length;i+=2)options[process.argv[i].replace(/^--/,'')]=process.argv[i+1];
const code=fs.readFileSync(options.reader,'utf8'),sha=s=>crypto.createHash('sha256').update(s).digest('hex');
const theory=`thm reading_function_reflexive:
    ? forall f fn(t R) R:
        f(0)=f(0)

thm reading_function_package:
    ? forall f fn(t R) R:
        1=1
        f(0)=f(0)

thm reading_function_value:
    ? forall f fn(t R) R:
        f(0) $in R

thm reading_function_three_results:
    ? forall f fn(t R) R:
        1=1
        f(0)=f(0)
        f(0) $in R
`;
const caller=call=>`claim:
    ? forall S set, f S:
        forall g S:
            g $in fn(t R) R
        =>:
            1=1
${call}
`;
const cases=[
 {name:'selected-equality',call:'    by thm reading_function_reflexive(f) => f(0)=f(0)',selected:true},
 {name:'selected-membership',call:'    by thm reading_function_value(f) => f(0) $in R',selected:true},
 {name:'release-first',call:'    release thm reading_function_reflexive(f)',index:0,pending:0},
 {name:'release-prefix',call:'    release thm reading_function_package(f)',index:1,pending:0},
 {name:'release-pending',call:'    release thm reading_function_three_results(f)',index:1,pending:1},
 {name:'selected-repair',call:'    f $in fn(t R) R\n    by thm reading_function_reflexive(f) => f(0)=f(0)',success:true},
 {name:'release-repair',call:'    f $in fn(t R) R\n    release thm reading_function_three_results(f)',success:true}
].filter(c=>!options.cases||options.cases.split(',').includes(c.name));
function records(b){const nodes=new Map(b.evidence_nodes.map(e=>[e.id,e.node]));function resolve(v){while(v?.kind==='evidence_reference')v=nodes.get(v.evidence_id);return v||{};}function result(v){let n=resolve(v);while(n.fields?.['0'])n=resolve(n.fields['0']);return n;}return{nodes,resolve,result};}
function post(payload){const url=new URL('/api/reading/build',options.endpoint);assert.equal(url.hostname,'127.0.0.1');return new Promise((resolve,reject)=>{const request=http.request(url,{method:'POST',headers:{'Content-Type':'application/json','Origin':url.origin}},response=>{const chunks=[];response.on('data',c=>chunks.push(c));response.on('end',()=>{try{assert.equal(response.statusCode,200);resolve(Buffer.concat(chunks).toString());}catch(error){reject(error);}});});request.on('error',reject);request.end(JSON.stringify(payload));});}
function fnv(value){let n=0xcbf29ce484222325n;for(const byte of Buffer.from(value))n=((n^BigInt(byte))*0x100000001b3n)&0xffffffffffffffffn;return 'fnv1a64:'+n.toString(16).padStart(16,'0');}
async function compile(item,mode){
 const source=caller(mode==='registered'?item.call.replaceAll('reading_function_','theory::reading_function_'):item.call),content=mode==='registered'?source:theory+'\n'+source,configuration='[export]\ntheory = "./theory.lit"\napplication = "./application.lit"\n';let raw;
 if(options.endpoint){const files=[{path:'application.lit',content}];if(mode==='registered')files.unshift({path:'theory.lit',content:theory},{path:'litex.config',content:configuration});raw=await post({language:'en',strict:true,entry:{kind:'file',path:'application.lit'},files});}
 else{
 const directory=fs.mkdtempSync(path.join(os.tmpdir(),'litex-theorem-closing-')),file=path.join(directory,'application.lit'),provider=path.join(directory,'theory.lit'),config=path.join(directory,'litex.config');
 try{
  fs.writeFileSync(file,content);
  if(mode==='registered'){fs.writeFileSync(provider,theory);fs.writeFileSync(config,configuration);}
  const command=[path.resolve(options.binary),'-reading','-json','-strict','-lang','en','-f',file],r=cp.spawnSync(command[0],command.slice(1),{encoding:'utf8',maxBuffer:32*1024*1024});assert(!r.error,String(r.error));assert.equal(r.status,item.success?0:1,r.stderr);raw=r.stdout;
 }finally{for(const p of [config,provider,file])if(fs.existsSync(p))fs.unlinkSync(p);fs.rmdirSync(directory);}
 }
 const b=JSON.parse(raw);assert.equal(b.run_result,item.success?'success':'failure');assert.equal(b.execution_policy.strict,true);assert.deepEqual(b.sources.map(s=>s.content),mode==='registered'?[theory,source]:[content]);for(const s of b.sources)assert.equal(s.digest,fnv(s.content));const rest={...b};delete rest.bundle_id;assert.equal(b.bundle_id,fnv(JSON.stringify(rest)));return b;
}
function mount(b,locale,editable){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 return {...dom,root,reader,row(s){const n=root.querySelector('[data-line="'+s.line+'"]');assert(n);return n;},async close(){await root.trigger('keydown',{key:'Escape'});},async hover(s,target=null,keyboard=false){target||=this.row(s).querySelector('.lr-source-code');if(keyboard)await this.row(s).querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},done(){assert.equal(JSON.stringify(b),before,'observer cannot change proof/source/publication');const source=b.sources.find(s=>s.id===reader.getSelection().source)||b.sources[0],text=root.querySelector('.lr-ide-input')?.value||source.content;assert.equal(root.querySelectorAll('.lr-code-row').length,text.split('\n').length,'explanations add no source rows');reader.destroy();}};
}
function owner(b){return b.statements.find(s=>s.status==='rejected'&&/\.(ByThmStmt|ReleaseThmStmt)$/.test(s.statement_kind));}
async function inspect(b,item,locale,editable){
 const s=owner(b),d=records(b),closing=d.result(s.evidence);assert.equal(closing.type,'TheoremInvocationClosingFailure');const f=d.resolve(closing.fields.failure);assert.equal(f.variant,item.selected?'ByThm':'Release');
 const v=mount(b,locale,editable);v.reader.selectStatement(s.id,s.line);await v.close();
 let card=await v.hover(s),part=card?.querySelector('.lr-theorem-failure');assert(part);assert.equal(part.dataset.stage,'Closing');assert.equal(part.dataset.status,'retained',item.name+': '+part.textContent);
 assert(part.querySelector('.lr-theorem-closing-note'));assert(part.querySelector('.lr-theorem-closing-goal').textContent.includes('f(0)'));
 assert(!/records were not fully retained|检查记录未完整保留|Earlier checks and their proofs do not fully correspond|先前检查及其证明未完整对应/.test(part.textContent));
 const tail=part.querySelector('.lr-theorem-failure-formation');assert(tail&&!tail.open);assert.equal(part.children.at(-1),tail);await tail.querySelector('summary').click();assert(tail.querySelector('.lr-theorem-wd-part[data-part="closing"]'));assert(!/not fully exported|未完整导出|No proof record can be matched/.test(tail.textContent),tail.textContent);
 for(const step of tail.querySelectorAll('.lr-proof-step').filter(n=>n.parentNode===tail))await step.querySelector('summary').click();
 const universal=tail.querySelector('.lr-forall-application');assert(universal,'argument type cites the actual caller forall');assert(universal.querySelector('.lr-forall-source .lr-fact-link'));assert(universal.querySelector('.lr-proof-substitutions'),'the source binder is paired with the actual function argument');
 if(item.selected){const selected=part.querySelector('.lr-theorem-closing-selection');assert(selected&&!selected.open);await selected.querySelector('summary').click();assert(selected.querySelector('.lr-fact-link'),'local selected proof cites this invocation return');}
 else{
  assert.equal(Number(part.dataset.closingIndex),item.index);const prefix=part.querySelector('.lr-theorem-closing-prefix'),pending=part.querySelector('.lr-theorem-closing-unchecked');
  if(item.index){assert(prefix&&!prefix.open);await prefix.querySelector('summary').click();assert(prefix.textContent.includes('1 = 1'));assert(!prefix.querySelector('.lr-fact-link'),'withdrawn closing prefix is not advertised as caller publication');}else assert(!prefix);
  if(item.pending){assert(pending&&!pending.open);await pending.querySelector('summary').click();assert(!pending.querySelector('.lr-fact-link,.lr-proof-step'),'unchecked caller suffix has no caller proof');}else assert(!pending);
 }
 await card.querySelector('.lr-proof-pin').click();const before=v.reader.getSelection();
 if(item.selected){const checked=d.resolve(d.resolve(closing.fields.checked).fields['0']),store=d.result(d.resolve(checked.fields.returned_conclusions[0]).fields.store),id=d.resolve(store.fields.fact_id||store.fields.whole_fact_id).fact_id,scope=d.resolve(closing.fields.local_env).scope_id,local=b.facts.find(f=>f.id===id);assert.equal(local?.scope_id,scope);const selection=v.root.querySelector('.lr-detail-body .lr-theorem-closing-selection');await selection.querySelector('summary').click();const reference=selection.querySelectorAll('.lr-fact-link').find(n=>n.dataset.fact===id);assert(reference,'selected proof cites its real local theorem return');await reference.click();assert.equal(v.reader.getSelection().fact,id);await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),before);assert(v.root.querySelector('.lr-detail-body .lr-theorem-closing-note'));}
 const link=v.root.querySelector('.lr-detail-body .lr-definition-link');assert(link);await link.click();assert(v.reader.getSelection().statement!==s.id);await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),before);assert(v.root.querySelector('.lr-detail-body .lr-theorem-closing-note'));await v.close();
 card=await v.hover(s,null,true);assert(card.querySelector('.lr-theorem-closing-note'));await v.close();
 const keyword=v.row(s).querySelector('[data-keyword="'+(item.selected?'by thm':'release thm')+'"]');assert(keyword);card=await v.hover(s,keyword);assert(card.querySelector('.lr-theorem-closing-note'));assert(card.querySelector('.lr-proof-symbol'));
 assert.equal(s.produced_fact_ids.length,0);assert.equal(s.inferred_fact_ids.length,0);assert(!v.row(s).querySelector('.lr-inference-toggle'));
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-proof-popover,.lr-diagnostic-point'));}v.done();
}
(async()=>{let contexts=0,views=0,corruptionControls=0;const observations=[],cache=new Map();
 for(const mode of options.modes?options.modes.split(','):['ordinary','registered'])for(const item of cases){const b=await compile(item,mode);cache.set(mode+':'+item.name,b);contexts++;if(item.success){assert(!b.statements.some(s=>s.status==='rejected'));continue;}for(const locale of ['zh','en'])for(const editable of [true,false]){await inspect(b,item,locale,editable);views++;}observations.push({case:item.name,mode,stage:'Closing',NativeSHA256:sha(JSON.stringify(b))});}
 if(!options.cases)for(const control of ['scope-owner','scope-parent','source','callee','checked-kind','invocation-kind','types','type-store','local-conclusion-wd','selected-proof','returned-store','failed-result','failed-subject','failed-object','failure-reason','diagnostic-phase','publication','closing-index','prefix-store','prefix-wd','pending-subject']){
  const prefix=['closing-index','prefix-store','prefix-wd','pending-subject'].includes(control),base=prefix?'release-pending':'selected-equality',cached=cache.get('ordinary:'+base)||cache.get('registered:'+base),b=structuredClone(cached),s=owner(b),d=records(b),context=d.result(s.evidence),f=context.fields,checked=d.resolve(f.checked),value=d.resolve(checked.fields['0']),invocation=prefix?value:d.resolve(value.fields.invocation),failed=d.resolve(f.failure),failure=d.result(failed.fields.result),prepared=d.resolve(f.prepared),scope=d.resolve(f.local_env);
  if(control==='scope-owner')b.scopes.find(x=>x.id===scope.scope_id).statement_id='foreign';if(control==='scope-parent')b.scopes.find(x=>x.id===scope.scope_id).parent_id='foreign';if(control==='source')d.resolve(d.resolve(f.origin).fields['0']).fields.line_file.source_id='foreign';if(control==='callee')d.resolve(d.resolve(f.callee).fields['0']).fields.name={kind:'symbol_reference',symbol_id:'foreign',name:'foreign'};if(control==='checked-kind')checked.variant='Future';if(control==='invocation-kind')invocation.type='FutureInvocation';if(control==='types')invocation.fields.type_checks=[];if(control==='type-store')delete d.resolve(invocation.fields.type_checks[0]).fields.stored;if(control==='local-conclusion-wd')invocation.fields.conclusions_wd=[];if(control==='selected-proof')delete value.fields.selected_proof;if(control==='returned-store')value.fields.returned_conclusions=[];if(control==='failed-result')delete failed.fields.result;if(control==='failed-subject')failure.fields.fact=prepared.fields.type_facts[0];if(control==='failed-object')failure.fields.failed_obj=d.result(prepared.fields.type_facts[0]).fields.set;if(control==='failure-reason')d.resolve(d.resolve(failure.fields.reason).fields['0']).fields.foreign=true;if(control==='diagnostic-phase')s.failure.phase='premise';if(control==='publication')s.produced_fact_ids=['foreign'];if(control==='closing-index')failed.fields.index='0';if(control==='prefix-store')failed.fields.stored=[];if(control==='prefix-wd')failed.fields.stored_wd=[invocation.fields.conclusions_wd[1]];if(control==='pending-subject')prepared.fields.conclusions[2]=prepared.fields.conclusions[0];
  const v=mount(b,'en',false);v.reader.selectStatement(s.id,s.line);await v.close();const card=await v.hover(s),part=card.querySelector('.lr-theorem-failure');assert(part,control);assert.equal(part.dataset.status,'incomplete',control);assert(!part.querySelector('.lr-theorem-closing-note,.lr-theorem-closing-prefix,.lr-theorem-closing-unchecked'),control);v.done();corruptionControls++;
 }
 const receipt={passed:true,actualSourceCases:cases.length,sourceContexts:contexts,views,corruptionControls,bilingualEditableReadOnly:true,actualClosingAndOuterFormation:true,completedLocalChecksAndWithdrawnPrefix:true,uncheckedCallerSuffix:true,WDLastClosed:true,definitionAndExactBack:true,noRejectedPublication:true,NativeUnchanged:true,readerSHA256:sha(code),rawNativeOnlyInMemory:true,actualCompilerPOSTs:options.endpoint?contexts:0,browserObserved:false,observations};
 if(options.receipt)fs.writeFileSync(options.receipt,JSON.stringify(receipt,null,2)+'\n');console.log(JSON.stringify(receipt));
})().catch(error=>{console.error(error);process.exitCode=1;});
