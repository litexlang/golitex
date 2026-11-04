'use strict';
// Actual expansion failures use typed stages; source code remains the interface.
const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),vm=require('node:vm'),http=require('node:http'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto'),{createDOM}=require('./dom.cjs');
const ROOT=path.resolve(__dirname,'../../../..');
const CASES=[
  {
    "name": "tuple-shape",
    "file": "examples/test_statements/negative/release_tuple_def_stmt/scalar.lit",
    "result": "failure",
    "route": "tuple",
    "stage": "Shape",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "tuple-domain",
    "file": "examples/test_statements/negative/release_tuple_def_stmt/invalid-wd.lit",
    "result": "failure",
    "route": "tuple",
    "stage": "Domain",
    "wd": true,
    "zeroCondition": true
  },
  {
    "name": "tuple-infinite",
    "file": "examples/test_statements/negative/release_tuple_def_stmt/infinite-domain.lit",
    "result": "failure",
    "route": "tuple",
    "stage": "Shape",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "struct-carrier",
    "file": "examples/test_statements/negative/release_struct_def_stmt/scalar-has-no-view.lit",
    "result": "failure",
    "route": "struct",
    "stage": "NoDefinitionOwnedCarrier",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "cart-wd",
    "file": "examples/test_statements/negative/release_cart_def_stmt/undefined-factor.lit",
    "result": "failure",
    "route": "cart",
    "stage": "FailToVerifyWellDefined",
    "wd": true,
    "zeroCondition": true
  },
  {
    "name": "range-membership",
    "file": "examples/test_statements/negative/expand_range_stmt/nonmember-range.lit",
    "result": "failure",
    "route": "range",
    "stage": "Membership",
    "wd": true,
    "zeroCondition": false
  },
  {
    "name": "set-direction",
    "file": "examples/test_statements/negative/by_extension_stmt/unequal-sets.lit",
    "result": "failure",
    "route": "set",
    "stage": "LeftToRight",
    "wd": true,
    "zeroCondition": false
  },
  {
    "name": "function-domain",
    "file": "examples/test_statements/negative/by_fn_extension_stmt/different-carriers.lit",
    "result": "failure",
    "route": "function",
    "stage": "DomainMatch",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "empty-range",
    "source": "expand: 1 $in range(0, 0)\n",
    "result": "failure",
    "route": "range",
    "stage": "Domain",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "range-wd",
    "source": "expand: 1 / 0 $in range(0, 2)\n",
    "result": "failure",
    "route": "range",
    "stage": "Membership",
    "wd": true,
    "zeroCondition": true
  },
  {
    "name": "parameter-release",
    "source": "claim:\n    ? forall reading_release_x R:\n        reading_release_x = reading_release_x\n    release obj def reading_release_x\n",
    "result": "failure",
    "route": "object",
    "stage": "ParamTypeNotReleasable",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "repeated-tuple-release",
    "source": "by enumerate finite_set:\n    ? forall reading_release_k {0, 1}:\n        reading_release_k = reading_release_k\n    release tuple def (1 / (1 - reading_release_k), 1)\n",
    "result": "failure",
    "route": "tuple",
    "stage": "Return",
    "wd": true,
    "zeroCondition": false
  },
  {
    "name": "set-right-direction",
    "source": "by extension {1} = {1, 2}\n",
    "result": "failure",
    "route": "set",
    "stage": "RightToLeft",
    "wd": true,
    "zeroCondition": false
  },
  {
    "name": "set-body-failure-block",
    "source": "by extension:\n    ? {1} = {1}\n    1 = 1\n    1 = 2\n",
    "result": "failure",
    "route": "set",
    "stage": "ProofBody",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "function-body-failure-block",
    "source": "by fn_extension:\n    ? (fn(x R) R {x}) = (fn(x R) R {x})\n    1 = 1\n    1 = 2\n",
    "result": "failure",
    "route": "function",
    "stage": "ProofBody",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "local-partial",
    "source": "claim:\n    ? 1 = 1\n    release tuple def (1, 2)\n    release tuple def 1\n",
    "result": "failure",
    "route": "tuple",
    "stage": "Shape",
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "set-goal-wd",
    "source": "by extension {1 / 0} = {1}\n",
    "result": "failure",
    "route": "set",
    "stage": "GoalWd",
    "wd": true,
    "zeroCondition": true
  },
  {
    "name": "function-goal-wd",
    "source": "by fn_extension (fn(x R) R {1 / 0}) = (fn(x R) R {x})\n",
    "result": "failure",
    "route": "function",
    "stage": "GoalWd",
    "wd": true,
    "zeroCondition": true
  },
  {
    "name": "function-no-interface",
    "source": "by fn_extension 1 = 1\n",
    "result": "failure",
    "route": "function",
    "stage": "DomainMatch",
    "noCandidates": true,
    "wd": false,
    "zeroCondition": false
  },
  {
    "name": "function-pointwise",
    "file": "examples/test_statements/negative/by_fn_extension_stmt/different-functions.lit",
    "result": "failure",
    "route": "function",
    "stage": "Pointwise",
    "wd": true
  },
  {
    "name": "repeated-tuple-success",
    "source": "by enumerate finite_set:\n    ? forall reading_release_j {0, 1}:\n        reading_release_j = reading_release_j\n    release tuple def (1, 2)\n",
    "result": "success",
    "positive": true
  },
  {
    "name": "range-success",
    "source": "expand: 1 $in range(0, 2)\n",
    "result": "success",
    "positive": true
  },
  {
    "name": "function-success",
    "source": "by fn_extension (fn(x R) R {x}) = (fn(x R) R {x})\n",
    "result": "success",
    "positive": true
  },
  {
    "name": "object-parse",
    "file": "examples/test_statements/negative/release_obj_def_stmt/undefined-object-definition.lit",
    "result": "failure",
    "parse": true
  },
  {
    "name": "unicode-range-membership",
    "source": "# 区间的成员关系\nexpand: 3 $in range(0, 2)\n",
    "result": "failure",
    "route": "range",
    "stage": "Membership",
    "wd": true
  },
  {
    "name": "tuple-function-construction",
    "source": "by fn_extension (1, 2) = (1, 2)\n",
    "result": "failure",
    "route": "function",
    "stage": "NoCompatibleFnSet",
    "wd": false
  },
  {
    "name": "tuple-fact-control",
    "source": "(1, 2) = (1, 2)\n",
    "result": "success",
    "factControl": true
  }
];
const options={binary:path.join(ROOT,'target/release/litex'),reader:path.join(__dirname,'../reader.js')};
if(require.main===module)for(let i=2;i<process.argv.length;i+=2){const key=process.argv[i].replace(/^--/,'');assert(['binary','reader','endpoint','cases'].includes(key)&&process.argv[i+1],'Usage: node expansion-failures.cjs [--binary litex] [--reader reader.js] [--endpoint http://127.0.0.1:port] [--cases name,...]');options[key]=process.argv[i+1];}
const code=fs.readFileSync(options.reader,'utf8'),sha=s=>crypto.createHash('sha256').update(s).digest('hex');
function fnv(s){let n=0xcbf29ce484222325n;for(const b of Buffer.from(s))n=((n^BigInt(b))*0x100000001b3n)&0xffffffffffffffffn;return'fnv1a64:'+n.toString(16).padStart(16,'0');}
function records(b){const nodes=new Map(b.evidence_nodes.map(n=>[n.id,n.node]));const resolve=v=>{const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};};const unwrap=v=>{let n=resolve(v),seen=new Set();while(n.fields?.['0']&&!seen.has(n)){seen.add(n);n=resolve(n.fields['0']);}return n;};return{nodes,resolve,unwrap};}
function post(payload){const url=new URL('/api/reading/build',options.endpoint);assert.equal(url.hostname,'127.0.0.1');return new Promise((resolve,reject)=>{const req=http.request(url,{method:'POST',headers:{'Content-Type':'application/json','Origin':url.origin}},res=>{const chunks=[];res.on('data',c=>chunks.push(c));res.on('end',()=>{try{assert.equal(res.statusCode,200);resolve(Buffer.concat(chunks).toString());}catch(e){reject(e);}});});req.on('error',reject);req.end(JSON.stringify(payload));});}
async function compile(item,mode){const source=item.source||fs.readFileSync(path.join(ROOT,item.file),'utf8');let raw;
 if(options.endpoint){const files=[{path:'candidate.lit',content:source}];if(mode==='registered')files.push({path:'litex.config',content:'[export]\nf0 = "./candidate.lit"\n'});raw=await post({language:'en',strict:true,entry:{kind:'file',path:'candidate.lit'},files});}
 else{const dir=fs.mkdtempSync(path.join(os.tmpdir(),'litex-expansion-failure-')),file=path.join(dir,'candidate.lit'),config=path.join(dir,'litex.config');try{fs.writeFileSync(file,source);if(mode==='registered')fs.writeFileSync(config,'[export]\nf0 = "./candidate.lit"\n');const r=cp.spawnSync(path.resolve(options.binary),['-reading','-json','-strict','-lang','en','-f',file],{encoding:'utf8',maxBuffer:32*1024*1024,timeout:120000});assert(!r.error,item.name+': '+r.error);assert.equal(r.status,item.result==='success'?0:1,item.name+': '+r.stderr);raw=r.stdout;}finally{if(fs.existsSync(config))fs.unlinkSync(config);fs.unlinkSync(file);fs.rmdirSync(dir);}}
 const b=JSON.parse(raw);assert.equal(b.run_result,item.result,item.name);assert(b.execution_policy.strict);assert.deepEqual(b.sources.map(s=>s.content),[source]);assert.equal(b.sources[0].digest,fnv(source));const clone={...b},identity=clone.bundle_id;delete clone.bundle_id;assert.equal(identity,fnv(JSON.stringify(clone)),item.name+': exact bundle digest');return b;
}
function mount(b,locale,editable){const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 const v={...dom,root,reader,row(s){const n=root.querySelector('[data-line="'+s.line+'"]');assert(n,s.id);return n;},async hover(s,target=null,keyboard=false){target||=v.row(s).querySelector('.lr-source-code');if(keyboard)await v.row(s).querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let k=0;k<3;k++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'Native source/proof/scope/publication remains unchanged');assert.equal(root.querySelectorAll('.lr-code-row').length,b.sources[0].content.split('\n').length);reader.destroy();}};return v;
}
const routes={tuple:'ReleaseAndExpand.ReleaseTupleDefStmt',struct:'ReleaseAndExpand.ReleaseStructDefStmt',cart:'ReleaseAndExpand.ReleaseCartDefStmt',object:'ReleaseAndExpand.ReleaseObjDefStmt',range:'ReleaseAndExpand.ExpandRangeStmt',set:'By.ByExtensionStmt',function:'By.ByFnExtensionStmt'};
async function inspect(item,b,locale,editable){const selected=b.statements.filter(s=>s.status==='rejected'&&s.statement_kind===routes[item.route]),v=mount(b,locale,editable);let interactions=0;
 if(item.parse){assert(b.diagnostics.some(d=>d.phase==='parse'));assert(!v.root.querySelector('.lr-expansion-failure'));v.done();return{views:0,interactions};}
 if(item.factControl){assert(b.statements.some(s=>s.statement_kind==='Fact'&&s.status==='accepted'));assert(!v.root.querySelector('.lr-expansion-failure'));v.done();return{views:0,interactions};}
 if(item.positive){const accepted=b.statements.filter(s=>s.status==='accepted'&&Object.values(routes).includes(s.statement_kind));assert(accepted.length);for(const s of accepted){await v.reader.selectStatement(s.id);assert(!v.root.querySelector('.lr-expansion-failure'));assert(v.root.querySelector('.lr-expansion-proof'),item.name+': accepted command remains an actual expansion view');await v.close();}v.done();return{views:accepted.length,interactions:accepted.length};}
 assert(selected.length,item.name+': actual rejected command');for(const s of selected){let card=await v.hover(s),part=card?.querySelector('.lr-expansion-failure');assert.equal(part?.dataset.status,'stage-retained',item.name+': '+part?.textContent);assert.equal(part.dataset.statement,s.id);assert.equal(part.dataset.route,item.route);assert.equal(part.dataset.stage,item.stage);assert(!part.textContent.includes('The current proof has not established this conclusion'));assert.equal(s.produced_fact_ids.length,0);assert.equal(s.inferred_fact_ids.length,0);assert(!v.row(s).querySelector('.lr-inference-toggle'));
  if(item.stage==='NoCompatibleFnSet'){assert(part.textContent.includes(locale==='zh'?'未能构造':'could not be constructed'));assert(!part.textContent.includes(locale==='zh'?'已匹配':'domains were matched'),'an older payload without prior matching evidence does not acquire that history');}
  const goal=part.querySelector('.lr-expansion-failed-goal');if(goal){assert(goal.dataset.fact);assert(!goal.querySelector('.lr-fact-link'),'an unproved target is not a published citation');assert(!/f\d+::/.test(goal.textContent),'public names are resolved');}
  const tail=part.querySelector('.lr-atomic-wd');if(item.wd){assert(tail&&!tail.open,item.name+': retained WD is final and closed');assert.equal(part.children.at(-1),tail);await tail.querySelector('summary').click();if(item.zeroCondition){assert(tail.querySelector('.lr-wd-unproved-conditions')?.textContent.includes('0 ≠ 0'),tail.textContent);}}else assert(!tail,item.name+': missing earlier WD is not reconstructed');
  if(item.name==='parameter-release')assert(part.querySelector('.lr-proof-context').textContent.includes('reading_release_x'));
  if(item.stage==='DomainMatch'){const details=part.querySelectorAll(':scope > details.lr-domain-candidate');if(item.noCandidates){assert.equal(details.length,0);assert(part.textContent.includes(locale==='zh'?'没有可展示的候选':'no candidate'));}else{assert(details.length);assert(part.querySelector('.lr-complete-domain'));assert(part.textContent.includes('R')&&part.textContent.includes('N'));if(details.length>1)assert(details.every(n=>!n.open));}}
  await card.querySelector('.lr-proof-pin').click();const before=v.reader.getSelection();assert.equal(before.statement,s.id);let pinned=v.root.querySelector('.lr-detail-body .lr-expansion-failure');assert.equal(pinned.dataset.statement,s.id);
  if(item.stage==='ProofBody'){const prefix=pinned.querySelector('.lr-expansion-checked-prefix');assert(prefix&&!prefix.open);await prefix.querySelector('summary').click();const step=prefix.querySelector('.lr-math-link');assert(step);await step.click();assert.equal(b.statements.find(n=>n.id===v.reader.getSelection().statement)?.status,'accepted');await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),before);pinned=v.root.querySelector('.lr-detail-body .lr-expansion-failure');const stop=pinned.querySelector('.lr-expansion-stop');assert(stop);const expected=stop.dataset.statement;await stop.click();assert.equal(v.reader.getSelection().statement,expected);assert.equal(b.statements.find(n=>n.id===expected)?.status,'rejected');await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),before);interactions+=6;}
  await v.close();assert((await v.hover(s,null,true)).querySelector('.lr-expansion-failure'));await v.close();const keyword=v.row(s).querySelector('[data-keyword]');if(keyword){card=await v.hover(s,keyword);assert.equal(card.querySelector('.lr-expansion-failure')?.dataset.statement,s.id);assert(card.querySelector('.lr-proof-symbol'));await v.close();}interactions+=3;
 }
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-expansion-failure,.lr-proof-popover,.lr-diagnostic-point'));}v.done();return{views:selected.length,interactions};
}
async function corruptionControls(){let checked=0;for(const control of ['root-type','dispatcher','result','failure-type','future-stage','leaf-payload','canonical','source-span','source-line','scope','origin','publication','inference','tokens','legacy']){const b=await compile(CASES.find(c=>c.name==='tuple-shape'),'ordinary'),d=records(b),s=b.statements.find(s=>s.status==='rejected'),root=d.resolve(s.evidence),dispatch=d.resolve(root.fields['0']),result=d.resolve(dispatch.fields['0']),failure=d.resolve(result.fields['0']);
  if(control==='root-type')root.type='FutureExecution';if(control==='dispatcher')dispatch.variant='CartDef';if(control==='result')result.variant='Success';if(control==='failure-type')failure.type='FutureTupleFailure';if(control==='future-stage')failure.variant='FutureStage';if(control==='leaf-payload')failure.fields={'0':'not an actual shape payload'};if(control==='canonical')s.source_statement_id='foreign';if(control==='source-span')s.start_byte++;if(control==='source-line')s.line++;if(control==='scope')s.scope_id='foreign';if(control==='origin')s.origin='generated';if(control==='publication')s.produced_fact_ids=['foreign'];if(control==='inference')s.inferred_fact_ids=['foreign'];if(control==='tokens')b.sources[0].tokens[0].text='let';if(control==='legacy')delete s.evidence;
  const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-expansion-failure');if(part){assert.equal(part.dataset.status,'incomplete',control);assert(!part.querySelector('.lr-expansion-failed-goal,.lr-atomic-wd,.lr-expansion-stop'),control);}v.done();checked++;
 }
 for(const[itemName,controls]of [['cart-wd',['missing-payload','missing-fact','failed-object-type','failed-object-family','reason-type','reason-missing']],['repeated-tuple-release',['missing-fact','wrong-result']],['set-body-failure-block',['prefix-count','child-ref','child-parent','body-text','prior-status']],['function-no-interface',['missing-domains','domains-type']]])for(const control of controls){
  const b=await compile(CASES.find(c=>c.name===itemName),'ordinary'),d=records(b),s=b.statements.find(s=>s.status==='rejected'&&s.statement_kind===routes[CASES.find(c=>c.name===itemName).route]);let node=d.resolve(s.evidence);for(let i=0;i<3;i++)node=d.resolve(node.fields['0']);const payload=d.resolve(node.fields['0']);
  if(itemName==='cart-wd'){if(control==='missing-payload')delete node.fields['0'];if(control==='missing-fact')delete payload.fields.fact;if(control==='failed-object-type')d.resolve(payload.fields.failed_obj).type='FutureObject';if(control==='failed-object-family')d.resolve(payload.fields.failed_obj).variant='Literal';if(control==='reason-type')d.resolve(payload.fields.reason).type='FutureReason';if(control==='reason-missing')delete payload.fields.reason;}
  if(itemName==='repeated-tuple-release'){if(control==='missing-fact')delete node.fields.fact;if(control==='wrong-result')node.fields.result={kind:'unavailable'};}
  if(itemName==='set-body-failure-block'){if(control==='prefix-count')payload.fields.step_index='99';if(control==='child-ref')payload.fields.result={kind:'unavailable'};if(control==='child-parent')b.statements.find(x=>x.id===payload.fields.result.statement_id).parent_statement_id='foreign';if(control==='body-text')d.resolve(payload.fields.statement).text='foreign';if(control==='prior-status')b.statements.find(x=>x.id===payload.fields.prior_steps[0].statement_id).status='rejected';}
  if(itemName==='function-no-interface'){if(control==='missing-domains')delete node.fields['0'];if(control==='domains-type')node.fields['0']={kind:'unavailable'};}
  const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-expansion-failure');assert(part);assert.equal(part.dataset.status,'incomplete',itemName+':'+control);assert(!part.querySelector('.lr-expansion-failed-goal,.lr-atomic-wd,.lr-expansion-stop'));v.done();checked++;
 }
 return checked;}
async function run(){let contexts=0,views=0,interactions=0;const receipts=[],selection=options.cases?new Set(options.cases.split(',')):null;
 for(const item of CASES.filter(c=>!selection||selection.has(c.name)))for(const mode of ['ordinary','registered']){const b=await compile(item,mode);for(const locale of ['zh','en'])for(const editable of [false,true]){const r=await inspect(item,b,locale,editable);views+=r.views;interactions+=r.interactions;}receipts.push({name:item.name,mode,result:b.run_result,NativeSHA256:sha(JSON.stringify(b))});contexts++;}
 const controls=selection?0:await corruptionControls();console.log(JSON.stringify({passed:true,sourceContexts:contexts,views,interactions,corruptionControls:controls,bilingualEditableReadOnly:true,typedStageAndNoPublication:true,actualBodyPrefixAndStopBack:true,WDLastAndClosedWhenRetained:true,missingHistoriesNotInvented:true,NativeUnchanged:true,actualCompilerPOSTs:options.endpoint?contexts+controls:0,readerSHA256:sha(code),rawNativeKeptInMemoryOnly:true,temporarySourceFilesRemoved:true,browserObserved:false,receipts}));
}
module.exports={cases:CASES};
if(require.main===module)run().catch(e=>{console.error(e);process.exitCode=1;});
