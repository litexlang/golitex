'use strict';
// Failed assumptions and discarded scratch scopes use actual execution evidence.
const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),vm=require('node:vm'),http=require('node:http'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto'),{createDOM}=require('./dom.cjs');
const ROOT=path.resolve(__dirname,'../../../..');
const CASES=[
  {
    "name": "trust-zero",
    "route": "trust",
    "source": "trust 1 / 0 = 0",
    "strict": false,
    "result": "failure",
    "zero": true
  },
  {
    "name": "trust-membership",
    "route": "trust",
    "source": "trust 1 / 0 $in R",
    "strict": false,
    "result": "failure",
    "zero": true
  },
  {
    "name": "trust-prefix",
    "route": "trust",
    "source": "trust:\n    2 = 2\n    1 / 0 = 0",
    "strict": false,
    "result": "failure",
    "zero": true
  },
  {
    "name": "trust-forall",
    "route": "trust",
    "source": "trust:\n    forall x R:\n        x / 0 = 0",
    "strict": false,
    "result": "failure",
    "zero": true,
    "quantified": true
  },
  {
    "name": "trust-assumed-false",
    "route": "trust",
    "source": "trust 1 = 2",
    "strict": false,
    "result": "success",
    "positive": true
  },
  {
    "name": "axiom-zero",
    "route": "axiom",
    "source": "axiom reading_bad:\n    ? forall x R:\n        x / 0 = 0",
    "strict": false,
    "result": "failure",
    "zero": true,
    "quantified": true
  },
  {
    "name": "axiom-parameter",
    "route": "axiom",
    "source": "axiom reading_bad:\n    ? forall x R / 0:\n        x = x",
    "strict": false,
    "result": "failure",
    "quantified": true
  },
  {
    "name": "axiom-accepted",
    "route": "axiom",
    "source": "axiom reading_refl:\n    ? forall x R:\n        x = x",
    "strict": false,
    "result": "success",
    "positive": true
  },
  {
    "name": "axiom-not-forall",
    "route": "axiom",
    "source": "axiom reading_bad:\n    ? 1 = 1",
    "strict": false,
    "result": "failure",
    "parse": true
  },
  {
    "name": "axiom-undefined",
    "route": "axiom",
    "source": "axiom reading_bad:\n    ? forall x R:\n        x = missing",
    "strict": false,
    "result": "failure",
    "parse": true
  },
  {
    "name": "axiom-duplicate",
    "route": "axiom",
    "source": "axiom reading_refl:\n    ? forall x R:\n        x = x\naxiom reading_refl:\n    ? forall x R:\n        x = x",
    "strict": false,
    "result": "failure",
    "parse": true
  },
  {
    "name": "strict-trust",
    "route": "trust",
    "source": "trust 1 = 1",
    "strict": true,
    "result": "failure",
    "terminal": true
  },
  {
    "name": "strict-axiom",
    "route": "axiom",
    "source": "axiom reading_refl:\n    ? forall x R:\n        x = x",
    "strict": true,
    "result": "failure",
    "terminal": true
  },
  {
    "name": "strict-trust-have",
    "route": "trust-have",
    "source": "trust have reading_assumed R",
    "strict": true,
    "result": "failure",
    "terminal": true
  },
  {
    "name": "sketch-false",
    "route": "sketch",
    "source": "sketch:\n    1 = 2",
    "strict": true,
    "result": "failure",
    "body": true,
    "prefix": false
  },
  {
    "name": "sketch-prefix",
    "route": "sketch",
    "source": "sketch:\n    2 + 2 = 4\n    1 = 2",
    "strict": true,
    "result": "failure",
    "body": true,
    "prefix": true
  },
  {
    "name": "sketch-nested",
    "route": "sketch",
    "source": "sketch:\n    2 = 2\n    sketch:\n        3 = 3\n        1 = 2",
    "strict": true,
    "result": "failure",
    "body": true,
    "prefix": true
  },
  {
    "name": "sketch-body-wd",
    "route": "sketch",
    "source": "sketch:\n    2 = 2\n    1 / 0 = 0",
    "strict": true,
    "result": "failure",
    "body": true,
    "prefix": true
  },
  {
    "name": "sketch-definition-prefix",
    "route": "sketch",
    "source": "sketch:\n    let reading_local = 2\n    reading_local + 1 = 3\n    1 = 2",
    "strict": true,
    "result": "failure",
    "body": true,
    "prefix": true
  },
  {
    "name": "sketch-claim",
    "route": "sketch",
    "source": "sketch:\n    2 = 2\n    claim:\n        ? 1 = 2\n        3 = 3",
    "strict": true,
    "result": "failure",
    "body": true,
    "prefix": true
  },
  {
    "name": "sketch-accepted",
    "route": "sketch",
    "source": "sketch:\n    2 = 2",
    "strict": true,
    "result": "success",
    "positive": true
  },
  {
    "name": "sketch-assumed-local",
    "route": "sketch",
    "source": "sketch:\n    trust 1 = 2\n    1 = 2",
    "strict": false,
    "result": "success",
    "positive": true
  },
  {
    "name": "sketch-assumption-noescape",
    "route": "sketch",
    "source": "sketch:\n    trust 1 = 2\n    1 = 2\n1 = 2",
    "strict": false,
    "result": "failure",
    "outerFailure": true,
    "positive": true
  },
  {
    "name": "sketch-name-noescape",
    "route": "sketch",
    "source": "sketch:\n    let reading_local = 1\nreading_local = 1",
    "strict": true,
    "result": "failure",
    "parse": true
  }
];
const options={binary:path.join(ROOT,'target/release/litex'),reader:path.join(__dirname,'../reader.js')};
if(require.main===module)for(let i=2;i<process.argv.length;i+=2){const key=process.argv[i].replace(/^--/,'');assert(['binary','reader','endpoint','cases'].includes(key)&&process.argv[i+1]);options[key]=process.argv[i+1];}
const code=fs.readFileSync(options.reader,'utf8'),sha=s=>crypto.createHash('sha256').update(s).digest('hex');
function fnv(s){let n=0xcbf29ce484222325n;for(const b of Buffer.from(s))n=((n^BigInt(b))*0x100000001b3n)&0xffffffffffffffffn;return'fnv1a64:'+n.toString(16).padStart(16,'0');}
function records(b){const nodes=new Map(b.evidence_nodes.map(n=>[n.id,n.node]));const resolve=v=>{const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};};const result=v=>{let n=resolve(v),seen=new Set();while(n.fields?.['0']&&!seen.has(n)){seen.add(n);n=resolve(n.fields['0']);}return n;};return{nodes,resolve,result};}
function post(payload){const url=new URL('/api/reading/build',options.endpoint);assert.equal(url.hostname,'127.0.0.1');return new Promise((resolve,reject)=>{const req=http.request(url,{method:'POST',headers:{'Content-Type':'application/json','Origin':url.origin}},res=>{const chunks=[];res.on('data',c=>chunks.push(c));res.on('end',()=>{try{assert.equal(res.statusCode,200);resolve(Buffer.concat(chunks).toString());}catch(e){reject(e);}});});req.on('error',reject);req.end(JSON.stringify(payload));});}
async function compile(item,mode='ordinary'){
 const source=item.source||fs.readFileSync(path.join(ROOT,item.file),'utf8'),strict=item.strict;let raw;
 if(options.endpoint){const files=[{path:'candidate.lit',content:source}];if(mode==='registered')files.push({path:'litex.config',content:'[export]\nf0 = "./candidate.lit"\n'});raw=await post({language:'en',strict,entry:{kind:'file',path:'candidate.lit'},files});}
 else{const dir=fs.mkdtempSync(path.join(os.tmpdir(),'litex-context-failure-')),file=path.join(dir,'candidate.lit'),config=path.join(dir,'litex.config');try{fs.writeFileSync(file,source);if(mode==='registered')fs.writeFileSync(config,'[export]\nf0 = "./candidate.lit"\n');const r=cp.spawnSync(path.resolve(options.binary),['-reading','-json',...(strict?['-strict']:[]),'-lang','en','-f',file],{encoding:'utf8',maxBuffer:32*1024*1024,timeout:120000});assert(!r.error,item.name+': '+r.error);assert.equal(r.status,item.result==='success'?0:1,item.name+': '+r.stderr);raw=r.stdout;}finally{if(fs.existsSync(config))fs.unlinkSync(config);fs.unlinkSync(file);fs.rmdirSync(dir);}}
 const b=JSON.parse(raw);assert.equal(b.run_result,item.result,item.name);assert.equal(b.execution_policy.strict,strict);assert.deepEqual(b.sources.map(s=>s.content),[source]);assert.equal(b.sources[0].digest,fnv(source));const clone={...b},identity=clone.bundle_id;delete clone.bundle_id;assert.equal(identity,fnv(JSON.stringify(clone)));return b;
}
function mount(b,locale,editable){const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 const v={...dom,root,reader,row(s){const n=root.querySelector('[data-line="'+s.line+'"]');assert(n,s.id);return n;},async hover(s,target=null,keyboard=false){target||=v.row(s).querySelector('.lr-source-code');if(keyboard)await v.row(s).querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let k=0;k<3;k++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'Native targets, proof, scopes and publication remain unchanged');assert.equal(root.querySelectorAll('.lr-code-row').length,b.sources[0].content.split('\n').length);reader.destroy();}};return v;
}
const routes={trust:'Trust.TrustStmt',axiom:'Definition.AxiomStmt',sketch:'ProofBlock.SketchStmt'};
const contextRows=(b,item)=>b.statements.filter(s=>s.statement_kind===routes[item.route]);
async function inspect(item,b,locale,editable){const v=mount(b,locale,editable);let interactions=0,views=0;
 if(item.terminal){assert.equal(b.statements.length,0,'policy rejection has no statement address');assert(b.diagnostics.some(d=>d.kind==='termination'));assert(!v.root.querySelector('.lr-context-failure,.lr-context-change-proof'));v.done();return{views,interactions};}
 if(item.parse){assert(b.diagnostics.some(d=>d.phase==='parse'));assert(!contextRows(b,item).some(s=>s.status==='rejected'),'parser rejection does not become an execution failure');assert(!v.root.querySelector('.lr-context-failure'));v.done();return{views,interactions};}
 const rows=contextRows(b,item);assert(rows.length,item.name);const d=records(b);
 for(const s of rows){let card=await v.hover(s);assert(card,item.name);views++;
  if(s.status==='accepted'){assert(item.positive);assert(card.querySelector('.lr-context-change-proof'));assert(!card.querySelector('.lr-context-failure'));if(item.route!=='sketch')assert(card.querySelector('.lr-explicit-assumption'),'accepted truth is explicitly assumed');else{assert.equal(s.produced_fact_ids.length,0);assert(!card.querySelector('.lr-atomic-wd'),'scratch block has no fabricated goal WD');}await v.close();continue;}
  const part=card.querySelector('.lr-context-failure');assert.equal(part?.dataset.status,'stage-retained',item.name+': '+card.textContent);assert.equal(part.dataset.route,item.route);assert.equal(part.dataset.statement,s.id);assert.equal(part.dataset.stage,item.route==='trust'?'WellDefined':item.route==='axiom'?'GoalWd':'ProofBody');assert(!card.querySelector('.lr-context-change-proof'));assert.equal(s.produced_fact_ids.length,0);assert.equal(s.inferred_fact_ids.length,0);assert(!v.row(s).querySelector('.lr-inference-toggle'));
  if(item.body){assert(!part.querySelector('.lr-atomic-wd'),'failed scratch body is not a closing-goal check');const prefix=part.querySelector('.lr-context-checked-prefix');assert.equal(!!prefix,!!item.prefix);if(prefix){assert(!prefix.open);await prefix.querySelector('summary').click();const link=prefix.querySelector('.lr-math-link');if(link){await card.querySelector('.lr-proof-pin').click();const before=v.reader.getSelection();await v.root.querySelector('.lr-detail-body .lr-context-checked-prefix .lr-math-link').click();assert.equal(b.statements.find(x=>x.id===v.reader.getSelection().statement)?.status,'accepted');await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),before);interactions+=3;await v.close();card=await v.hover(s);}else assert.equal(prefix.dataset.sourceStatus,'not-exported');}
   await card.querySelector('.lr-proof-pin').click();const before=v.reader.getSelection(),stop=v.root.querySelector('.lr-detail-body .lr-context-stop');assert(stop);const target=stop.dataset.statement;await stop.click();assert.equal(v.reader.getSelection().statement,target);assert.equal(b.statements.find(x=>x.id===target).status,'rejected');await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),before);interactions+=3;
  }else{const tail=part.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);await tail.querySelector('summary').click();if(item.zero){const text=tail.textContent;assert(text.includes('0 ≠ 0'),text);}assert(!part.querySelector('.lr-context-properties,.lr-explicit-assumption'),'rejected assumption publishes no accepted-assumption card');if(item.quantified)assert(part.querySelector('.lr-quantifier-formation-failure'),'keep existing binder/check evidence');interactions++;}
  await v.close();assert((await v.hover(s,null,true)).querySelector('.lr-context-failure'));await v.close();const token=v.row(s).querySelector('[data-keyword]');if(token){assert((await v.hover(s,token)).querySelector('.lr-context-failure'));await v.close();}interactions+=2;
 }
 if(item.outerFailure){const s=b.statements.find(s=>s.statement_kind==='Fact'&&s.parent_statement_id===null&&s.status==='rejected');assert(s,'local assumed false equality does not escape');assert(!s.produced_fact_ids.length);}
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-proof-popover,.lr-context-failure,.lr-diagnostic-point'));}v.done();return{views,interactions};
}
async function controls(cache){let checked=0;
 for(const name of ['trust-zero','axiom-zero','sketch-prefix'])for(const control of ['root-type','dispatcher','result','missing-payload','source-span','source-line','scope','origin','canonical','tokens','publication','inference','legacy',...(name==='sketch-prefix'?[]:['policy'])]){
  const item=CASES.find(c=>c.name===name),b=JSON.parse(cache.get(name)),d=records(b),s=contextRows(b,item).find(s=>s.status==='rejected'),root=d.resolve(s.evidence),dispatch=d.resolve(root.fields['0']),result=d.resolve(dispatch.fields['0']);
  if(control==='policy')b.execution_policy.strict=true;if(control==='root-type')root.type='FutureExecution';if(control==='dispatcher')dispatch.variant='Foreign';if(control==='result')result.variant='Success';if(control==='missing-payload')delete result.fields['0'];if(control==='source-span')s.start_byte++;if(control==='source-line')s.line++;if(control==='scope')s.scope_id='foreign';if(control==='origin')s.origin='generated';if(control==='canonical')s.source_statement_id='foreign';if(control==='tokens')b.sources[0].tokens[0].text='let';if(control==='publication')s.produced_fact_ids=['foreign'];if(control==='inference')s.inferred_fact_ids=['foreign'];if(control==='legacy')delete s.evidence;
  const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-context-failure');if(part){assert.equal(part.dataset.status,'incomplete',name+':'+control);assert(!part.querySelector('.lr-context-failed-goal,.lr-atomic-wd,.lr-context-stop,.lr-quantifier-formation-failure'));}v.done();checked++;
 }
 for(const control of ['prefix-index','prior-kind','child-parent','child-scope','prior-scope','failed-text']){const item=CASES.find(c=>c.name==='sketch-prefix'),b=JSON.parse(cache.get(item.name)),d=records(b),s=contextRows(b,item)[0],body=d.result(s.evidence),f=body.fields;if(control==='prefix-index')f.step_index='99';if(control==='prior-kind')f.prior_steps[0]={kind:'unavailable'};if(control==='child-scope')b.statements.find(x=>x.id===f.result.statement_id).scope_id='foreign';if(control==='prior-scope')b.statements.find(x=>x.id===f.prior_steps[0].statement_id).scope_id='foreign';if(control==='child-parent')b.statements.find(x=>x.id===f.result.statement_id).parent_statement_id='foreign';if(control==='failed-text')d.resolve(f.statement).text='foreign';const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-context-failure');assert.equal(part.dataset.status,'incomplete');assert(!part.querySelector('.lr-context-stop,.lr-context-checked-prefix'));v.done();checked++;}
 return checked;
}
async function run(){let contexts=0,views=0,interactions=0;const receipts=[],cache=new Map(),selection=options.cases?new Set(options.cases.split(',')):null;
 for(const item of CASES.filter(c=>!selection||selection.has(c.name)))for(const mode of ['ordinary','registered']){const b=await compile(item,mode);if(mode==='ordinary')cache.set(item.name,JSON.stringify(b));for(const locale of ['zh','en'])for(const editable of [false,true]){const r=await inspect(item,b,locale,editable);views+=r.views;interactions+=r.interactions;}receipts.push({name:item.name,mode,result:b.run_result,strict:item.strict,NativeSHA256:sha(JSON.stringify(b))});contexts++;}
 const corruptions=selection?0:await controls(cache);console.log(JSON.stringify({passed:true,sourceContexts:contexts,views,interactions,corruptionControls:corruptions,typedFailureRoutes:['trust.WellDefined','axiom.GoalWd','sketch.ProofBody'],bilingualEditableReadOnly:true,assumptionNotProof:true,strictTerminationHasNoStatementAddress:true,existingQuantifierHistoryPreserved:true,localPrefixStopAndExactBack:true,unpublishedFailureAndNoScopeEscape:true,WDLastAndClosedWhenRetained:true,NativeUnchanged:true,actualCompilerPOSTs:options.endpoint?contexts:0,readerSHA256:sha(code),rawNativeInMemoryOnly:true,temporarySourceFilesRemoved:true,browserObserved:false,receipts}));
}
module.exports={cases:CASES};if(require.main===module)run().catch(e=>{console.error(e);process.exitCode=1;});
