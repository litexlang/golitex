'use strict';
// Actual foundation failures retain their prerequisite, local body stop and WD.
const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),vm=require('node:vm'),http=require('node:http'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto'),{createDOM}=require('./dom.cjs');
const ROOT=path.resolve(__dirname,'../../../..');
const CASES=[
  {
    "name": "release_regularity_axiom_stmt-empty-set-has-no-regularity-witness",
    "file": "examples/test_statements/negative/release_regularity_axiom_stmt/empty-set-has-no-regularity-witness.lit",
    "result": "failure",
    "parse": false,
    "route": "regularity",
    "stage": "Nonempty",
    "index": null,
    "positive": false,
    "wd": true,
    "zero": false,
    "prefix": false
  },
  {
    "name": "release_regularity_axiom_stmt-undefined-set",
    "file": "examples/test_statements/negative/release_regularity_axiom_stmt/undefined-set.lit",
    "result": "failure",
    "parse": true
  },
  {
    "name": "release_regularity_axiom_stmt-wrong-arity",
    "file": "examples/test_statements/negative/release_regularity_axiom_stmt/wrong-arity.lit",
    "result": "failure",
    "parse": true
  },
  {
    "name": "release_axiom_of_choice_stmt-family-with-empty-member",
    "file": "examples/test_statements/negative/release_axiom_of_choice_stmt/family-with-empty-member.lit",
    "result": "failure",
    "parse": false,
    "route": "choice",
    "stage": "ProofBody",
    "index": null,
    "positive": false,
    "wd": false,
    "zero": false,
    "prefix": false
  },
  {
    "name": "release_axiom_of_choice_stmt-undefined-family",
    "file": "examples/test_statements/negative/release_axiom_of_choice_stmt/undefined-family.lit",
    "result": "failure",
    "parse": true
  },
  {
    "name": "release_zorn_lemma_stmt-unary-order-interface",
    "file": "examples/test_statements/negative/release_zorn_lemma_stmt/unary-order-interface.lit",
    "result": "failure",
    "parse": false,
    "route": "zorn",
    "stage": "PropInterface",
    "index": null,
    "positive": false,
    "wd": false,
    "zero": false,
    "prefix": false
  },
  {
    "name": "release_zorn_lemma_stmt-undefined-zorn-interfaces",
    "file": "examples/test_statements/negative/release_zorn_lemma_stmt/undefined-zorn-interfaces.lit",
    "result": "failure",
    "parse": false,
    "route": "zorn",
    "stage": "PropInterface",
    "index": null,
    "positive": false,
    "wd": false,
    "zero": false,
    "prefix": false
  },
  {
    "name": "regularity-positive",
    "source": "release regularity_axiom({1})\n",
    "result": "success",
    "route": "regularity",
    "stage": "",
    "index": null,
    "positive": true,
    "wd": false,
    "zero": false,
    "prefix": false
  },
  {
    "name": "regularity-wd",
    "source": "release regularity_axiom(1 / 0)\n",
    "result": "failure",
    "route": "regularity",
    "stage": "SetWd",
    "index": null,
    "positive": false,
    "wd": true,
    "zero": true,
    "prefix": false
  },
  {
    "name": "choice-member-obligation",
    "source": "release axiom_of_choice: set {{}}:\n    1 = 1\n",
    "result": "failure",
    "route": "choice",
    "stage": "Obligation",
    "index": 1,
    "positive": false,
    "wd": true,
    "zero": false,
    "prefix": false
  },
  {
    "name": "choice-set-obligation",
    "source": "release axiom_of_choice: set 1:\n    1 = 1\n",
    "result": "failure",
    "route": "choice",
    "stage": "Obligation",
    "index": 1,
    "positive": false,
    "wd": true,
    "zero": false,
    "prefix": false
  },
  {
    "name": "choice-wd",
    "source": "release axiom_of_choice: set 1 / 0:\n    1 = 1\n",
    "result": "failure",
    "route": "choice",
    "stage": "FamilyWd",
    "index": null,
    "positive": false,
    "wd": true,
    "zero": true,
    "prefix": false
  },
  {
    "name": "choice-body-prefix",
    "source": "release axiom_of_choice: set {{1}}:\n    1 = 1\n    1 = 2\n",
    "result": "failure",
    "route": "choice",
    "stage": "ProofBody",
    "index": null,
    "positive": false,
    "wd": false,
    "zero": false,
    "prefix": true
  },
  {
    "name": "zorn-body-prefix",
    "source": "have reading_zorn_carrier set\nabstract_prop reading_zorn_order(x, y)\nprop reading_zorn_bound(c power_set(reading_zorn_carrier), u reading_zorn_carrier):\n    forall x c:\n        $reading_zorn_order(x, u)\nprop reading_zorn_maximal(m reading_zorn_carrier):\n    forall x reading_zorn_carrier:\n        $reading_zorn_order(m, x)\n        =>:\n            x = m\nrelease zorn_lemma: set reading_zorn_carrier, prop reading_zorn_order, prop reading_zorn_bound, prop reading_zorn_maximal:\n    1 = 1\n    1 = 2\n",
    "result": "failure",
    "route": "zorn",
    "stage": "ProofBody",
    "index": null,
    "positive": false,
    "wd": false,
    "zero": false,
    "prefix": true
  },
  {
    "name": "zorn-nonempty-obligation",
    "source": "have reading_zorn_carrier set\nabstract_prop reading_zorn_order(x, y)\nprop reading_zorn_bound(c power_set(reading_zorn_carrier), u reading_zorn_carrier):\n    forall x c:\n        $reading_zorn_order(x, u)\nprop reading_zorn_maximal(m reading_zorn_carrier):\n    forall x reading_zorn_carrier:\n        $reading_zorn_order(m, x)\n        =>:\n            x = m\nrelease zorn_lemma: set reading_zorn_carrier, prop reading_zorn_order, prop reading_zorn_bound, prop reading_zorn_maximal:\n    1 = 1\n",
    "result": "failure",
    "route": "zorn",
    "stage": "Obligation",
    "index": 0,
    "positive": false,
    "wd": true,
    "zero": false,
    "prefix": false
  },
  {
    "name": "zorn-wd",
    "source": "have reading_zorn_carrier set\nabstract_prop reading_zorn_order(x, y)\nprop reading_zorn_bound(c power_set(reading_zorn_carrier), u reading_zorn_carrier):\n    forall x c:\n        $reading_zorn_order(x, u)\nprop reading_zorn_maximal(m reading_zorn_carrier):\n    forall x reading_zorn_carrier:\n        $reading_zorn_order(m, x)\n        =>:\n            x = m\nrelease zorn_lemma: set 1 / 0, prop reading_zorn_order, prop reading_zorn_bound, prop reading_zorn_maximal:\n    1 = 1\n",
    "result": "failure",
    "route": "zorn",
    "stage": "SetWd",
    "index": null,
    "positive": false,
    "wd": true,
    "zero": true,
    "prefix": false
  },
  {
    "name": "zorn-obligation-1",
    "source": "have reading_zorn_carrier set\nabstract_prop reading_zorn_order(x, y)\nprop reading_zorn_bound(c power_set(reading_zorn_carrier), u reading_zorn_carrier):\n    forall x c:\n        $reading_zorn_order(x, u)\nprop reading_zorn_maximal(m reading_zorn_carrier):\n    forall x reading_zorn_carrier:\n        $reading_zorn_order(m, x)\n        =>:\n            x = m\nclaim:\n    ? forall:\n        $is_nonempty_set(reading_zorn_carrier)\n        =>:\n            exist m reading_zorn_carrier st {$reading_zorn_maximal(m)}\n    release zorn_lemma: set reading_zorn_carrier, prop reading_zorn_order, prop reading_zorn_bound, prop reading_zorn_maximal:\n        1 = 1\n",
    "result": "failure",
    "route": "zorn",
    "stage": "Obligation",
    "index": 1,
    "positive": false,
    "wd": true,
    "zero": false,
    "prefix": false
  },
  {
    "name": "zorn-obligation-2",
    "source": "have reading_zorn_carrier set\nabstract_prop reading_zorn_order(x, y)\nprop reading_zorn_bound(c power_set(reading_zorn_carrier), u reading_zorn_carrier):\n    forall x c:\n        $reading_zorn_order(x, u)\nprop reading_zorn_maximal(m reading_zorn_carrier):\n    forall x reading_zorn_carrier:\n        $reading_zorn_order(m, x)\n        =>:\n            x = m\nclaim:\n    ? forall:\n        $is_nonempty_set(reading_zorn_carrier)\n        forall x reading_zorn_carrier:\n            $reading_zorn_order(x, x)\n        =>:\n            exist m reading_zorn_carrier st {$reading_zorn_maximal(m)}\n    release zorn_lemma: set reading_zorn_carrier, prop reading_zorn_order, prop reading_zorn_bound, prop reading_zorn_maximal:\n        1 = 1\n",
    "result": "failure",
    "route": "zorn",
    "stage": "Obligation",
    "index": 2,
    "positive": false,
    "wd": true,
    "zero": false,
    "prefix": false
  },
  {
    "name": "zorn-obligation-3",
    "source": "have reading_zorn_carrier set\nabstract_prop reading_zorn_order(x, y)\nprop reading_zorn_bound(c power_set(reading_zorn_carrier), u reading_zorn_carrier):\n    forall x c:\n        $reading_zorn_order(x, u)\nprop reading_zorn_maximal(m reading_zorn_carrier):\n    forall x reading_zorn_carrier:\n        $reading_zorn_order(m, x)\n        =>:\n            x = m\nclaim:\n    ? forall:\n        $is_nonempty_set(reading_zorn_carrier)\n        forall x reading_zorn_carrier:\n            $reading_zorn_order(x, x)\n        forall x, y, z reading_zorn_carrier:\n            $reading_zorn_order(x, y)\n            $reading_zorn_order(y, z)\n            =>:\n                $reading_zorn_order(x, z)\n        =>:\n            exist m reading_zorn_carrier st {$reading_zorn_maximal(m)}\n    release zorn_lemma: set reading_zorn_carrier, prop reading_zorn_order, prop reading_zorn_bound, prop reading_zorn_maximal:\n        1 = 1\n",
    "result": "failure",
    "route": "zorn",
    "stage": "Obligation",
    "index": 3,
    "positive": false,
    "wd": true,
    "zero": false,
    "prefix": false
  },
  {
    "name": "zorn-obligation-4",
    "source": "have reading_zorn_carrier set\nabstract_prop reading_zorn_order(x, y)\nprop reading_zorn_bound(c power_set(reading_zorn_carrier), u reading_zorn_carrier):\n    forall x c:\n        $reading_zorn_order(x, u)\nprop reading_zorn_maximal(m reading_zorn_carrier):\n    forall x reading_zorn_carrier:\n        $reading_zorn_order(m, x)\n        =>:\n            x = m\nclaim:\n    ? forall:\n        $is_nonempty_set(reading_zorn_carrier)\n        forall x reading_zorn_carrier:\n            $reading_zorn_order(x, x)\n        forall x, y, z reading_zorn_carrier:\n            $reading_zorn_order(x, y)\n            $reading_zorn_order(y, z)\n            =>:\n                $reading_zorn_order(x, z)\n        forall x, y reading_zorn_carrier:\n            $reading_zorn_order(x, y)\n            $reading_zorn_order(y, x)\n            =>:\n                x = y\n        =>:\n            exist m reading_zorn_carrier st {$reading_zorn_maximal(m)}\n    release zorn_lemma: set reading_zorn_carrier, prop reading_zorn_order, prop reading_zorn_bound, prop reading_zorn_maximal:\n        1 = 1\n",
    "result": "failure",
    "route": "zorn",
    "stage": "Obligation",
    "index": 4,
    "positive": false,
    "wd": true,
    "zero": false,
    "prefix": false
  },
  {
    "name": "zorn-obligation-5",
    "source": "have reading_zorn_carrier set\nabstract_prop reading_zorn_order(x, y)\nprop reading_zorn_bound(c power_set(reading_zorn_carrier), u reading_zorn_carrier):\n    forall x c:\n        $reading_zorn_order(x, u)\nprop reading_zorn_maximal(m reading_zorn_carrier):\n    forall x reading_zorn_carrier:\n        $reading_zorn_order(m, x)\n        =>:\n            x = m\nclaim:\n    ? forall:\n        $is_nonempty_set(reading_zorn_carrier)\n        forall x reading_zorn_carrier:\n            $reading_zorn_order(x, x)\n        forall x, y, z reading_zorn_carrier:\n            $reading_zorn_order(x, y)\n            $reading_zorn_order(y, z)\n            =>:\n                $reading_zorn_order(x, z)\n        forall x, y reading_zorn_carrier:\n            $reading_zorn_order(x, y)\n            $reading_zorn_order(y, x)\n            =>:\n                x = y\n        forall c power_set(reading_zorn_carrier):\n            forall x, y c:\n                $reading_zorn_order(x, y) or $reading_zorn_order(y, x)\n            =>:\n                exist u reading_zorn_carrier st {$reading_zorn_bound(c, u)}\n        =>:\n            exist m reading_zorn_carrier st {$reading_zorn_maximal(m)}\n    release zorn_lemma: set reading_zorn_carrier, prop reading_zorn_order, prop reading_zorn_bound, prop reading_zorn_maximal:\n        1 = 1\n",
    "result": "success",
    "route": "zorn",
    "stage": "",
    "index": null,
    "positive": true,
    "wd": false,
    "zero": false,
    "prefix": false
  },
  {
    "name": "choice-positive",
    "source": "release axiom_of_choice: set {{1}}:\n    forall A {{1}}:\n        $is_nonempty_set(A)\n",
    "result": "success",
    "route": "choice",
    "stage": "",
    "index": null,
    "positive": true,
    "wd": false,
    "zero": false,
    "prefix": false
  }
,
{
  "name": "local-partial-regularity",
  "source": "claim:\n    ? 1 = 1\n    release regularity_axiom({1})\n    release regularity_axiom({})\n",
  "result": "failure",
  "route": "regularity",
  "stage": "Nonempty",
  "index": null,
  "positive": false,
  "mixed": true,
  "wd": true,
  "zero": false,
  "prefix": false,
  "expectedAccepted": 1
},
{
  "name": "repeated-regularity-success",
  "source": "by enumerate finite_set:\n    ? forall reading_regularity_k {0, 1}:\n        reading_regularity_k = reading_regularity_k\n    release regularity_axiom({reading_regularity_k})\n",
  "result": "success",
  "route": "regularity",
  "stage": "",
  "index": null,
  "positive": true,
  "mixed": false,
  "wd": false,
  "zero": false,
  "prefix": false,
  "expectedAccepted": 2
}
];
const options={binary:path.join(ROOT,'target/release/litex'),reader:path.join(__dirname,'../reader.js')};
if(require.main===module)for(let i=2;i<process.argv.length;i+=2){const key=process.argv[i].replace(/^--/,'');assert(['binary','reader','endpoint','cases'].includes(key)&&process.argv[i+1]);options[key]=process.argv[i+1];}
const code=fs.readFileSync(options.reader,'utf8'),sha=s=>crypto.createHash('sha256').update(s).digest('hex');
function fnv(s){let n=0xcbf29ce484222325n;for(const b of Buffer.from(s))n=((n^BigInt(b))*0x100000001b3n)&0xffffffffffffffffn;return'fnv1a64:'+n.toString(16).padStart(16,'0');}
function records(b){const nodes=new Map(b.evidence_nodes.map(n=>[n.id,n.node]));const resolve=v=>{const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};};const result=v=>{let n=resolve(v),seen=new Set();while(n.fields?.['0']&&!seen.has(n)){seen.add(n);n=resolve(n.fields['0']);}return n;};return{nodes,resolve,result};}
function post(payload){const url=new URL('/api/reading/build',options.endpoint);assert.equal(url.hostname,'127.0.0.1');return new Promise((resolve,reject)=>{const req=http.request(url,{method:'POST',headers:{'Content-Type':'application/json','Origin':url.origin}},res=>{const chunks=[];res.on('data',c=>chunks.push(c));res.on('end',()=>{try{assert.equal(res.statusCode,200);resolve(Buffer.concat(chunks).toString());}catch(e){reject(e);}});});req.on('error',reject);req.end(JSON.stringify(payload));});}
async function compile(item,mode='ordinary'){
 const source=item.source||fs.readFileSync(path.join(ROOT,item.file),'utf8');let raw;
 if(options.endpoint){const files=[{path:'candidate.lit',content:source}];if(mode==='registered')files.push({path:'litex.config',content:'[export]\nf0 = "./candidate.lit"\n'});raw=await post({language:'en',strict:true,entry:{kind:'file',path:'candidate.lit'},files});}
 else{const dir=fs.mkdtempSync(path.join(os.tmpdir(),'litex-foundation-failure-')),file=path.join(dir,'candidate.lit'),config=path.join(dir,'litex.config');try{fs.writeFileSync(file,source);if(mode==='registered')fs.writeFileSync(config,'[export]\nf0 = "./candidate.lit"\n');const r=cp.spawnSync(path.resolve(options.binary),['-reading','-json','-strict','-lang','en','-f',file],{encoding:'utf8',maxBuffer:32*1024*1024,timeout:120000});assert(!r.error,item.name+': '+r.error);assert.equal(r.status,item.result==='success'?0:1,item.name+': '+r.stderr);raw=r.stdout;}finally{if(fs.existsSync(config))fs.unlinkSync(config);fs.unlinkSync(file);fs.rmdirSync(dir);}}
 const b=JSON.parse(raw);assert.equal(b.run_result,item.result,item.name);assert(b.execution_policy.strict);assert.deepEqual(b.sources.map(s=>s.content),[source]);assert.equal(b.sources[0].digest,fnv(source));const clone={...b},identity=clone.bundle_id;delete clone.bundle_id;assert.equal(identity,fnv(JSON.stringify(clone)));return b;
}
function mount(b,locale,editable){const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 const v={...dom,root,reader,row(s){const n=root.querySelector('[data-line="'+s.line+'"]');assert(n,s.id);return n;},async hover(s,target=null,keyboard=false){target||=v.row(s).querySelector('.lr-source-code');if(keyboard)await v.row(s).querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let k=0;k<3;k++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'Native targets, proof, scopes and publication remain unchanged');assert.equal(root.querySelectorAll('.lr-code-row').length,b.sources[0].content.split('\n').length);reader.destroy();}};return v;
}
const routes={regularity:'ReleaseAndExpand.ReleaseRegularityAxiomStmt',choice:'ReleaseAndExpand.ReleaseAxiomOfChoiceStmt',zorn:'ReleaseAndExpand.ReleaseZornLemmaStmt'};
async function inspect(item,b,locale,editable){const v=mount(b,locale,editable);let interactions=0;
 if(item.parse){assert(b.diagnostics.some(d=>d.phase==='parse'));assert(!b.statements.some(s=>Object.values(routes).includes(s.statement_kind)));assert(!v.root.querySelector('.lr-foundation-failure'));v.done();return{views:0,interactions};}
 const selected=b.statements.filter(s=>s.statement_kind===routes[item.route]&&['accepted','rejected'].includes(s.status));assert(selected.length,item.name);if(item.expectedAccepted)assert.equal(selected.filter(s=>s.status==='accepted').length,item.expectedAccepted);
 for(const s of selected){let card=await v.hover(s);assert(card,item.name);if(s.status==='accepted'){assert(item.positive||item.mixed);await v.reader.selectStatement(s.id);assert.equal(v.reader.getSelection().statement,s.id);const part=v.root.querySelector('.lr-detail-body .lr-foundation-proof');assert(part,item.name+': actual selected foundation execution');assert(!v.root.querySelector('.lr-detail-body .lr-foundation-failure'));assert(part.querySelectorAll('.lr-command-conclusion .lr-fact-link').some(n=>s.produced_fact_ids.includes(n.dataset.fact)),item.name+': selected execution keeps its own published result');await v.close();interactions+=2;continue;}
  assert.equal(s.status,'rejected');const part=card.querySelector('.lr-foundation-failure');assert.equal(part?.dataset.status,'stage-retained',item.name+': stage='+part?.dataset.stage+' '+card.textContent);assert.equal(part.dataset.statement,s.id);assert.equal(part.dataset.route,item.route);assert.equal(part.dataset.stage,item.stage);assert.equal(s.produced_fact_ids.length,0);assert.equal(s.inferred_fact_ids.length,0);assert(!v.row(s).querySelector('.lr-inference-toggle'));assert(part.querySelector('.lr-foundation-origin'));
  const goal=part.querySelector('.lr-foundation-failed-goal');if(['Nonempty','Obligation'].includes(item.stage)){assert(goal?.dataset.fact);assert(!goal.querySelector('.lr-fact-link'),'unproved prerequisite is not a published citation');assert(!/f\d+::/.test(goal.textContent));if(item.index!==null)assert.equal(goal.dataset.obligationIndex,String(item.index));}
  const tail=part.querySelector('.lr-atomic-wd');if(item.wd){assert(tail&&!tail.open,item.name+': final closed formation');assert.equal(part.children.at(-1),tail);await tail.querySelector('summary').click();if(item.zero)assert(tail.querySelector('.lr-wd-unproved-conditions')?.textContent.includes('0 ≠ 0'),tail.textContent);interactions++;}else assert(!tail,item.name+': absent earlier WD is not reconstructed');
  if(item.stage==='PropInterface'){const detail=part.querySelector('.lr-failure-details');assert(detail&&!detail.open);await detail.querySelector('summary').click();assert(detail.querySelector('.lr-failure-message').textContent.includes('release zorn_lemma'));interactions++;}
  await card.querySelector('.lr-proof-pin').click();const before=v.reader.getSelection();assert.equal(before.statement,s.id);let pinned=v.root.querySelector('.lr-detail-body .lr-foundation-failure');assert(pinned);
  if(item.stage==='ProofBody'){if(item.prefix){const prefix=pinned.querySelector('.lr-foundation-checked-prefix');assert(prefix&&!prefix.open);await prefix.querySelector('summary').click();assert.equal(prefix.dataset.sourceStatus,'not-exported');assert(prefix.textContent.includes('1 = 1')||prefix.textContent.includes('1 = 1'.replaceAll(' ','')));assert(!prefix.querySelector('.lr-math-link'),'no fabricated source link for unexported successful execution');interactions++;}const stop=pinned.querySelector('.lr-foundation-stop');assert(stop);const expected=stop.dataset.statement;await stop.click();assert.equal(v.reader.getSelection().statement,expected);assert.equal(b.statements.find(n=>n.id===expected)?.status,'rejected');await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),before);interactions+=2;}
  await v.close();assert((await v.hover(s,null,true)).querySelector('.lr-foundation-failure'));await v.close();const keyword=v.row(s).querySelector('[data-keyword]');if(keyword){card=await v.hover(s,keyword);assert.equal(card.querySelector('.lr-foundation-failure')?.dataset.statement,s.id);await v.close();}interactions+=3;
 }
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-foundation-failure,.lr-proof-popover,.lr-diagnostic-point'));}v.done();return{views:selected.length,interactions};
}
async function corruptionControls(){let checked=0;for(const control of ['root-type','dispatcher','result','failure-type','future-stage','missing-payload','payload-type','source-span','source-line','scope','origin','origin-checked','canonical','tokens','publication','inference','legacy']){
 const b=await compile(CASES.find(c=>c.name==='regularity-wd')),d=records(b),s=b.statements.find(s=>s.status==='rejected');let n=d.resolve(s.evidence);const root=n,dispatch=d.resolve(n.fields['0']),result=d.resolve(dispatch.fields['0']),failure=d.resolve(result.fields['0']);
 if(control==='root-type')root.type='FutureExecution';if(control==='dispatcher')dispatch.variant='AxiomOfChoice';if(control==='result')result.variant='Success';if(control==='failure-type')failure.type='FutureFoundationFailure';if(control==='future-stage')failure.variant='FutureStage';if(control==='missing-payload')delete failure.fields['0'];if(control==='payload-type')d.resolve(failure.fields['0']).type='FutureObjectCheck';if(control==='source-span')s.start_byte++;if(control==='source-line')s.line++;if(control==='scope')s.scope_id='foreign';if(control==='origin')s.origin='generated';if(control==='origin-checked')s.origin='checked';if(control==='canonical')s.source_statement_id='foreign';if(control==='tokens')b.sources[0].tokens[0].text='let';if(control==='publication')s.produced_fact_ids=['foreign'];if(control==='inference')s.inferred_fact_ids=['foreign'];if(control==='legacy')delete s.evidence;
 const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-foundation-failure');if(part){assert.equal(part.dataset.status,'incomplete',control);assert(!part.querySelector('.lr-foundation-failed-goal,.lr-atomic-wd,.lr-foundation-stop'));}v.done();checked++;
 }
 for(const[name,controls]of [['choice-member-obligation',['index-missing','index-outside','goal-id','goal-type','goal-source','result-type']],['choice-body-prefix',['prefix-count','prior-type','child-ref','child-parent','body-text']],['release_zorn_lemma_stmt-unary-order-interface',['message-type','message-empty']]])for(const control of controls){
  const item=CASES.find(c=>c.name===name),b=await compile(item),d=records(b),s=b.statements.find(s=>s.status==='rejected'&&s.statement_kind===routes[item.route]);let n=d.resolve(s.evidence);for(let i=0;i<3;i++)n=d.resolve(n.fields['0']);const payload=d.resolve(n.fields['0']||n.fields.result);
  if(control==='index-missing')delete n.fields.index;if(control==='index-outside')n.fields.index='99';if(control==='goal-id')delete d.result(d.result(n.fields.result).fields.fact).fields.fact_id;if(control==='goal-type')d.result(d.result(n.fields.result).fields.fact).type='FutureFact';if(control==='goal-source')d.result(d.result(n.fields.result).fields.fact).fields.line_file={source_id:'foreign',line:1};if(control==='result-type')payload.type='FutureFactCheck';if(control==='prefix-count')payload.fields.step_index='99';if(control==='prior-type'){const ref=payload.fields.prior_steps[0];if(ref.kind==='statement_reference')b.statements.find(x=>x.id===ref.statement_id).status='rejected';else d.resolve(ref).type='FutureExecution';}if(control==='child-ref')payload.fields.result={kind:'unavailable'};if(control==='child-parent')b.statements.find(x=>x.id===payload.fields.result.statement_id).parent_statement_id='foreign';if(control==='body-text')d.resolve(payload.fields.statement).text='foreign';if(control==='message-type')n.fields['0']={kind:'unavailable'};if(control==='message-empty')n.fields['0']='';
  const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-foundation-failure');assert(part);assert.equal(part.dataset.status,'incomplete',control);assert(!part.querySelector('.lr-foundation-failed-goal,.lr-atomic-wd,.lr-foundation-stop'));v.done();checked++;
 }
 return checked;
}
async function run(){let contexts=0,views=0,interactions=0;const receipts=[],selection=options.cases?new Set(options.cases.split(',')):null;
 for(const item of CASES.filter(c=>!selection||selection.has(c.name)))for(const mode of ['ordinary','registered']){const b=await compile(item,mode);for(const locale of ['zh','en'])for(const editable of [false,true]){const r=await inspect(item,b,locale,editable);views+=r.views;interactions+=r.interactions;}receipts.push({name:item.name,mode,result:b.run_result,NativeSHA256:sha(JSON.stringify(b))});contexts++;}
 const controls=selection?0:await corruptionControls();console.log(JSON.stringify({passed:true,sourceContexts:contexts,views,interactions,corruptionControls:controls,actualObservedRouteStages:[...new Set(CASES.filter(c=>!c.positive&&!c.parse).map(c=>c.route+'.'+c.stage))],bilingualEditableReadOnly:true,prerequisitesUnpublished:true,actualBodyPrefixAndStopBack:true,unexportedPrefixSourceNotFabricated:true,WDLastAndClosedWhenRetained:true,NativeUnchanged:true,actualCompilerPOSTs:options.endpoint?contexts+controls:0,readerSHA256:sha(code),rawNativeKeptInMemoryOnly:true,temporarySourceFilesRemoved:true,browserObserved:false,receipts}));
}
module.exports={cases:CASES};if(require.main===module)run().catch(e=>{console.error(e);process.exitCode=1;});
