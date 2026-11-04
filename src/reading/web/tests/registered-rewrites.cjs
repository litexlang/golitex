'use strict';
// Actual reflexivity/permutation certificates; never replace the selected proof.
const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),vm=require('node:vm'),http=require('node:http'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto'),{createDOM}=require('./dom.cjs');
const ROOT=path.resolve(__dirname,'../../../..');
const CASES=[
  {
    "name": "reflexivity",
    "source": "prop reading_eq(x, y set):\n    x = y\n\nregister reflexive:\n    ? forall x set:\n        $reading_eq(x, x)\n\nprop reading_guard(x R):\n    x > 0\n\nhave reading_f fn(x R: $reading_guard(x)) R\n\n$reading_eq(reading_f(1), reading_f(1))\n",
    "result": "success",
    "variant": "Reflexivity",
    "expected": 1
  },
  {
    "name": "reflexivity-definition-control",
    "source": "prop reading_eq(x, y set):\n    x = y\n\nregister reflexive:\n    ? forall x set:\n        $reading_eq(x, x)\n\nprop reading_guard(x R):\n    x > 0\n\nhave reading_f fn(x R: $reading_guard(x)) R\n\n$reading_eq(1, 1)\n",
    "result": "success",
    "variant": null,
    "expected": 0
  },
  {
    "name": "reflexivity-missing-registration",
    "source": "prop reading_eq(x, y set):\n    x = y\n\nprop reading_guard(x R):\n    x > 0\n\nhave reading_f fn(x R: $reading_guard(x)) R\n\n$reading_eq(reading_f(1), reading_f(1))\n",
    "result": "failure",
    "variant": null,
    "expected": 0
  },
  {
    "name": "reflexivity-later-reuse",
    "source": "prop reading_eq(x, y set):\n    x = y\n\nregister reflexive:\n    ? forall x set:\n        $reading_eq(x, x)\n\nprop reading_guard(x R):\n    x > 0\n\nhave reading_f fn(x R: $reading_guard(x)) R\n\n$reading_eq(reading_f(1), reading_f(1))\n\n$reading_eq(reading_f(1), reading_f(1))\n",
    "result": "success",
    "variant": "Reflexivity",
    "expected": 1,
    "reuse": true
  },
  {
    "name": "reflexivity-local-prefix",
    "source": "prop reading_eq(x, y set):\n    x = y\n\nregister reflexive:\n    ? forall x set:\n        $reading_eq(x, x)\n\nprop reading_guard(x R):\n    x > 0\n\nhave reading_f fn(x R: $reading_guard(x)) R\n\nclaim:\n    ? 1 = 2\n    $reading_eq(reading_f(2), reading_f(2))\n",
    "result": "failure",
    "variant": "Reflexivity",
    "expected": 1,
    "localFailure": true
  },
  {
    "name": "symmetry",
    "source": "prop reading_mutual(A, B set):\n    A $subset B\n    B $subset A\n\nregister symmetric:\n    ? forall A, B set:\n        $reading_mutual(A, B)\n        =>:\n            $reading_mutual(B, A)\n\nprop reading_pair(A, B set):\n    $reading_mutual(A, B)\n\nstrategy reading_pair_swap:\n    ? forall A, B set:\n        $reading_pair(A, B)\n        =>:\n            $reading_pair(B, A)\n    $reading_mutual(A, B)\n    $reading_mutual(B, A)\n    by def $reading_pair(B, A)\n\nregister symmetric:\n    ? forall A, B set:\n        $reading_pair(A, B)\n        =>:\n            $reading_pair(B, A)\n\nclaim:\n    ? forall A, B set:\n        A $subset B\n        B $subset A\n        =>:\n            $reading_pair(B, A)\n    by def $reading_mutual(A, B)\n    $reading_pair(B, A)\n",
    "result": "success",
    "variant": "Symmetry",
    "expected": 1,
    "permutation": [
      1,
      0
    ]
  },
  {
    "name": "symmetry-missing-registration",
    "source": "prop reading_mutual(A, B set):\n    A $subset B\n    B $subset A\n\nregister symmetric:\n    ? forall A, B set:\n        $reading_mutual(A, B)\n        =>:\n            $reading_mutual(B, A)\n\nprop reading_pair(A, B set):\n    $reading_mutual(A, B)\n\nstrategy reading_pair_swap:\n    ? forall A, B set:\n        $reading_pair(A, B)\n        =>:\n            $reading_pair(B, A)\n    $reading_mutual(A, B)\n    $reading_mutual(B, A)\n    by def $reading_pair(B, A)\n\nclaim:\n    ? forall A, B set:\n        A $subset B\n        B $subset A\n        =>:\n            $reading_pair(B, A)\n    by def $reading_mutual(A, B)\n    $reading_pair(B, A)\n",
    "result": "failure",
    "variant": null,
    "expected": 0
  },
  {
    "name": "symmetry-definition-control",
    "source": "# Node: atomic.ByKnownRewrite.Symmetry\n# Run: litex -f examples/proof_nodes/atomic/by_known_rewrite/symmetry.lit\n#\n# Registers symmetric swap for `same`, then proves the swap forall\n# (parameter types must be `set` for `register symmetric`).\n\nprop same(x set, y set):\n    x = y\n\nregister symmetric:\n    ? forall x, y set:\n        $same(x, y)\n        =>:\n            $same(y, x)\n\nforall x, y set:\n    $same(x, y)\n    =>:\n        $same(y, x)\n",
    "result": "success",
    "variant": null,
    "expected": 0
  },
  {
    "name": "symmetry-local-prefix",
    "source": "prop reading_mutual(A, B set):\n    A $subset B\n    B $subset A\n\nregister symmetric:\n    ? forall A, B set:\n        $reading_mutual(A, B)\n        =>:\n            $reading_mutual(B, A)\n\nprop reading_pair(A, B set):\n    $reading_mutual(A, B)\n\nstrategy reading_pair_swap:\n    ? forall A, B set:\n        $reading_pair(A, B)\n        =>:\n            $reading_pair(B, A)\n    $reading_mutual(A, B)\n    $reading_mutual(B, A)\n    by def $reading_pair(B, A)\n\nregister symmetric:\n    ? forall A, B set:\n        $reading_pair(A, B)\n        =>:\n            $reading_pair(B, A)\n\nclaim:\n    ? 1 = 2\n    claim:\n        ? forall A, B set:\n            A $subset B\n            B $subset A\n            =>:\n                $reading_pair(B, A)\n        by def $reading_mutual(A, B)\n        $reading_pair(B, A)\n",
    "result": "failure",
    "variant": "Symmetry",
    "expected": 1,
    "permutation": [
      1,
      0
    ],
    "localFailure": true
  },
  {
    "name": "cyclic-permutation",
    "source": "prop reading_cycle(a, b, c set):\n    a $subset b\n    b $subset c\n    c $subset a\n\nregister symmetric:\n    ? forall a, b, c set:\n        $reading_cycle(a, b, c)\n        =>:\n            $reading_cycle(b, c, a)\n\nprop reading_orbit(a, b, c set):\n    $reading_cycle(a, b, c)\n\nstrategy reading_orbit_rotate:\n    ? forall a, b, c set:\n        $reading_orbit(a, b, c)\n        =>:\n            $reading_orbit(b, c, a)\n    $reading_cycle(a, b, c)\n    $reading_cycle(b, c, a)\n    by def $reading_orbit(b, c, a)\n\nregister symmetric:\n    ? forall a, b, c set:\n        $reading_orbit(a, b, c)\n        =>:\n            $reading_orbit(b, c, a)\n\nclaim:\n    ? forall a, b, c set:\n        a $subset b\n        b $subset c\n        c $subset a\n        =>:\n            $reading_orbit(c, a, b)\n    by def $reading_cycle(a, b, c)\n    $reading_orbit(c, a, b)\n",
    "result": "success",
    "variant": "Symmetry",
    "expected": 1,
    "permutation": [
      1,
      2,
      0
    ]
  },
  {
    "name": "cyclic-missing-registration",
    "source": "prop reading_cycle(a, b, c set):\n    a $subset b\n    b $subset c\n    c $subset a\n\nregister symmetric:\n    ? forall a, b, c set:\n        $reading_cycle(a, b, c)\n        =>:\n            $reading_cycle(b, c, a)\n\nprop reading_orbit(a, b, c set):\n    $reading_cycle(a, b, c)\n\nstrategy reading_orbit_rotate:\n    ? forall a, b, c set:\n        $reading_orbit(a, b, c)\n        =>:\n            $reading_orbit(b, c, a)\n    $reading_cycle(a, b, c)\n    $reading_cycle(b, c, a)\n    by def $reading_orbit(b, c, a)\n\nclaim:\n    ? forall a, b, c set:\n        a $subset b\n        b $subset c\n        c $subset a\n        =>:\n            $reading_orbit(c, a, b)\n    by def $reading_cycle(a, b, c)\n    $reading_orbit(c, a, b)\n",
    "result": "failure",
    "variant": null,
    "expected": 0
  }
];
const options={binary:path.join(ROOT,'target/release/litex'),reader:path.join(__dirname,'../reader.js')};
if(require.main===module)for(let i=2;i<process.argv.length;i+=2){const key=process.argv[i].replace(/^--/,'');assert(['binary','reader','endpoint','cases'].includes(key)&&process.argv[i+1]);options[key]=process.argv[i+1];}
const code=fs.readFileSync(options.reader,'utf8'),sha=s=>crypto.createHash('sha256').update(s).digest('hex');
function fnv(s){let n=0xcbf29ce484222325n;for(const b of Buffer.from(s))n=((n^BigInt(b))*0x100000001b3n)&0xffffffffffffffffn;return'fnv1a64:'+n.toString(16).padStart(16,'0');}
function records(b){const nodes=new Map(b.evidence_nodes.map(n=>[n.id,n.node]));const resolve=v=>{const seen=new Set();while(v?.kind==='evidence_reference'&&!seen.has(v.evidence_id)){seen.add(v.evidence_id);v=nodes.get(v.evidence_id);}return v||{};};const result=v=>{let n=resolve(v),seen=new Set();while(n.fields?.['0']&&!seen.has(n)){seen.add(n);n=resolve(n.fields['0']);}return n;};return{nodes,resolve,result};}
function post(payload){const url=new URL('/api/reading/build',options.endpoint);assert.equal(url.hostname,'127.0.0.1');return new Promise((resolve,reject)=>{const req=http.request(url,{method:'POST',headers:{'Content-Type':'application/json','Origin':url.origin}},res=>{const chunks=[];res.on('data',c=>chunks.push(c));res.on('end',()=>{try{assert.equal(res.statusCode,200);resolve(Buffer.concat(chunks).toString());}catch(e){reject(e);}});});req.on('error',reject);req.end(JSON.stringify(payload));});}
async function compile(item,mode='ordinary'){
 const source=item.source||fs.readFileSync(path.join(ROOT,item.file),'utf8'),strict=true;let raw;
 if(options.endpoint){const files=[{path:'candidate.lit',content:source}];if(mode==='registered')files.push({path:'litex.config',content:'[export]\nf0 = "./candidate.lit"\n'});raw=await post({language:'en',strict,entry:{kind:'file',path:'candidate.lit'},files});}
 else{const dir=fs.mkdtempSync(path.join(os.tmpdir(),'litex-registered-rewrite-')),file=path.join(dir,'candidate.lit'),config=path.join(dir,'litex.config');try{fs.writeFileSync(file,source);if(mode==='registered')fs.writeFileSync(config,'[export]\nf0 = "./candidate.lit"\n');const r=cp.spawnSync(path.resolve(options.binary),['-reading','-json',...(strict?['-strict']:[]),'-lang','en','-f',file],{encoding:'utf8',maxBuffer:32*1024*1024,timeout:120000});assert(!r.error,item.name+': '+r.error);assert.equal(r.status,item.result==='success'?0:1,item.name+': '+r.stderr);raw=r.stdout;}finally{if(fs.existsSync(config))fs.unlinkSync(config);fs.unlinkSync(file);fs.rmdirSync(dir);}}
 const b=JSON.parse(raw);assert.equal(b.run_result,item.result,item.name);assert.equal(b.execution_policy.strict,strict);assert.deepEqual(b.sources.map(s=>s.content),[source]);assert.equal(b.sources[0].digest,fnv(source));const clone={...b},identity=clone.bundle_id;delete clone.bundle_id;assert.equal(identity,fnv(JSON.stringify(clone)));return b;
}
function mount(b,locale,editable){const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;vm.runInContext(code,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 const v={...dom,root,reader,row(s){const n=root.querySelector('[data-line="'+s.line+'"]');assert(n,s.id);return n;},async hover(s,target=null,keyboard=false){target||=v.row(s).querySelector('.lr-source-code');if(keyboard)await v.row(s).querySelector('.lr-line-number').trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let k=0;k<3;k++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'Native targets, proof, scopes and publication remain unchanged');assert.equal(root.querySelectorAll('.lr-code-row').length,(b.sources.find(source=>source.id===reader.getSelection().source)||b.sources[0]).content.split('\n').length);reader.destroy();}};return v;
}
function frames(d,v){const out=[],seen=new Set();for(let n=d.resolve(v);n&&!seen.has(n);n=d.resolve(n.fields?.searched_proof||n.fields?.['0'])){seen.add(n);out.push(n);if(!n.fields?.searched_proof&&!n.fields?.['0'])break;}return out;}
function applications(b,d){const out=new Map();for(const[id,n]of d.nodes)if(n.type==='VerifyAtomicExceptEqualityFactSuccess'){const route=frames(d,n.fields.searched_proof).find(n=>n.type==='AtomicExceptEqualityFactSearchProofByKnownRewrite'&&['Reflexivity','Symmetry'].includes(n.variant));if(!route)continue;const goal=d.result(n.fields.fact),raw=b.facts.find(f=>f.id===goal.fields.fact_id.fact_id);assert(raw);const owner=raw.producer_statement_id||b.scopes.find(s=>s.id===raw.scope_id)?.statement_id;out.set(raw.id,{fact:{...raw,producer_statement_id:owner,evidence:{kind:'evidence_reference',evidence_id:id}},root:n,route,detail:d.resolve(route.fields['0'])});}return[...out.values()];}
async function inspect(item,b,locale,editable){const d=records(b),apps=applications(b,d),v=mount(b,locale,editable);assert.equal(apps.length,item.expected,item.name);let interactions=0;
 for(const app of apps){const{fact,route,detail}=app;assert.equal(route.variant,item.variant);let card=await v.hover(fact),part=card?.querySelector('.lr-registered-rewrite');assert.equal(part?.dataset.status,'retained',item.name+': '+card?.textContent);assert.equal(part.dataset.targetFact,fact.id);assert.equal(part.dataset.rule,route.type+'::'+route.variant);assert.equal(part.dataset.predicate,detail.fields.cite_prop.symbol_id);assert(!part.querySelector('.lr-registration-source-link'),'native certificate has no exact registration-statement identity');const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);assert(!/f\d+::/.test(part.textContent));
  if(item.variant==='Reflexivity'){assert(!part.querySelector('.lr-proof-step,.lr-registered-permutation'));assert(part.querySelector('.lr-reflexive-argument'));}
  else{assert.deepEqual(JSON.parse(part.dataset.permutation),item.permutation);assert.equal(part.querySelectorAll('.lr-permutation-argument').length,item.permutation.length);const check=part.querySelector('.lr-proof-step');assert(check&&!check.open);await check.querySelector('summary').click();assert(!/cannot be matched|未完整导出/.test(check.textContent),check.textContent);assert(check.querySelector('.lr-predicate-application'));assert(check.querySelector('.lr-atomic-wd')&&!check.querySelector('.lr-atomic-wd').open);const alternate=d.result(detail.fields.alternate_fact),alternateId=alternate.fields.fact_id.fact_id;assert(!b.statements.some(s=>s.produced_fact_ids.includes(alternateId)),'derived alternate is not a published conclusion');for(let pass=0;pass<3;pass++){const pending=check.querySelectorAll('details.lr-proof-step').filter(n=>!n.open&&!n.closest('.lr-atomic-wd'));if(!pending.length)break;for(const child of pending)await child.querySelector('summary').click();}assert(part.querySelectorAll('.lr-fact-link').every(link=>link.dataset.fact!==alternateId));const cited=check.querySelector('.lr-fact-link');assert(cited,'the actual base-relation citation is retained inside the alternate proof');const citedId=cited.dataset.fact;await cited.click();assert.equal(v.reader.getSelection().fact,citedId);await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().focusLine,fact.line);await v.close();card=await v.hover(fact);part=card.querySelector('.lr-registered-rewrite');interactions+=3;}
  const definition=part.querySelector('.lr-registered-definition');assert(definition);await card.querySelector('.lr-proof-pin').click();const before=v.reader.getSelection();assert.equal(before.focusLine,fact.line);const pinned=v.root.querySelector('.lr-detail-body .lr-registered-rewrite');await pinned.querySelector('.lr-registered-definition').click();assert.equal(v.reader.getSelection().statement,b.symbols.find(s=>s.id===detail.fields.cite_prop.symbol_id).definition_statement_id);await v.root.querySelector('.lr-back').click();assert.deepEqual(v.reader.getSelection(),before);assert(v.root.querySelector('.lr-detail-body .lr-registered-rewrite'));await v.close();interactions+=3;
  card=await v.hover(fact,null,true);assert(card.querySelector('.lr-registered-rewrite'));await v.close();const symbol=v.row(fact).querySelector('[data-symbol]');if(symbol){card=await v.hover(fact,symbol);assert(card.querySelector('.lr-registered-rewrite'));await v.close();}interactions+=2;
 }
 const registration=b.statements.find(s=>s.status==='accepted'&&s.source_id===v.reader.getSelection().source&&s.statement_kind==='Register.RegisterSymmetricPropStmt');if(registration){const keyword=v.row(registration).querySelector('[data-keyword="register symmetric"]');assert(keyword);const card=await v.hover(registration,keyword),help=card.querySelector('.lr-proof-symbol');assert(help);assert(help.textContent.includes(locale==='zh'?'至少两个形参':'at least two set-kind parameters'));assert(help.textContent.includes(locale==='zh'?'循环置换':'cyclic permutations'));await v.close();interactions++;}
 if(item.reuse){const s=b.statements.findLast(s=>s.statement_kind==='Fact'&&s.status==='accepted');const card=await v.hover(s);assert(!card.querySelector('.lr-registered-rewrite'),'later known-fact reuse keeps its own route');assert(card.querySelector('.lr-known-application'));await v.close();}
 if(item.localFailure){assert(b.statements.some(s=>s.status==='rejected'&&s.statement_kind==='ProofBlock.ClaimStmt'));for(const s of b.statements.filter(s=>s.status==='rejected'))assert(!s.produced_fact_ids.length);}
 if(!apps.length){const s=b.statements.findLast(s=>s.statement_kind==='Fact'||s.status==='rejected');if(s){const card=await v.hover(s);assert(!card?.querySelector('.lr-registered-rewrite'),'definition/failure is not relabeled as registered rewrite');await v.close();}}
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-proof-popover,.lr-registered-rewrite'));}v.done();return{applications:apps.length,interactions};
}
async function corrupt(cache){let count=0;for(const name of ['reflexivity','symmetry'])for(const control of ['root-type','goal-missing','goal-id','goal-predicate','unknown-predicate','predicate-kind','owner','target-scope','native-detail','missing-detail','route-type','goal-location','argument-text',...(name==='reflexivity'?['unequal-arguments']:['missing-permutation','identity-permutation','duplicate-permutation','out-of-range-permutation','wrong-alternate','failed-alternate-proof','missing-alternate-proof','mismatched-alternate-proof'])]){
 const b=JSON.parse(cache.get(name)),d=records(b),app=applications(b,d)[0],{fact,root,route,detail}=app,goal=d.result(root.fields.fact);if(control==='root-type')root.type='FutureProof';if(control==='goal-missing')delete root.fields.fact;if(control==='goal-id')goal.fields.fact_id={kind:'fact_identity',fact_id:'foreign'};if(control==='goal-predicate')goal.fields.predicate={kind:'symbol_reference',symbol_id:'foreign',name:'foreign'};if(control==='unknown-predicate')detail.fields.cite_prop={kind:'symbol_reference',symbol_id:'foreign',name:'foreign'};if(control==='predicate-kind')b.symbols.find(s=>s.id===detail.fields.cite_prop.symbol_id).kind='BuiltinThm';if(control==='owner')b.statements.find(s=>s.id===fact.producer_statement_id).scope_id='foreign';if(control==='target-scope')b.scopes.find(s=>s.id===fact.scope_id).parent_id='foreign';if(control==='native-detail')detail.type='FutureRegisteredProof';if(control==='missing-detail')delete route.fields['0'];if(control==='route-type')route.type='FutureRewrite';if(control==='argument-text')delete d.resolve(goal.fields.body[0]).text;if(control==='goal-location')goal.fields.line_file={source_id:'foreign',line:1};if(control==='unequal-arguments')goal.fields.body[1]={kind:'unavailable'};if(control==='missing-permutation')delete detail.fields.argument_permutation;if(control==='identity-permutation')detail.fields.argument_permutation=['0','1'];if(control==='duplicate-permutation')detail.fields.argument_permutation=['0','0'];if(control==='out-of-range-permutation')detail.fields.argument_permutation=['1','9'];if(control==='wrong-alternate')d.result(detail.fields.alternate_fact).fields.body.reverse();if(control==='failed-alternate-proof')d.result(detail.fields.proof_of_alternate_fact).type='VerifyAtomicExceptEqualityFactFailed';if(control==='missing-alternate-proof')delete detail.fields.proof_of_alternate_fact;if(control==='mismatched-alternate-proof')d.result(detail.fields.proof_of_alternate_fact).fields.fact={kind:'unavailable'};
 const v=mount(b,'en',false);await v.reader.selectFact(fact.id);const part=v.root.querySelector('.lr-registered-rewrite');if(part){assert.equal(part.dataset.status,'incomplete',name+':'+control);assert(!part.querySelector('.lr-proof-step,.lr-formula,.lr-definition-link'),'incomplete data cannot draw a derivation');}v.done();count++;
 }return count;}
async function run(){let contexts=0,views=0,interactions=0,actualApplications=0;const receipts=[],cache=new Map(),selected=options.cases?new Set(options.cases.split(',')):null;for(const item of CASES.filter(c=>!selected||selected.has(c.name)))for(const mode of ['ordinary','registered']){const b=await compile(item,mode);if(mode==='ordinary')cache.set(item.name,JSON.stringify(b));for(const locale of ['zh','en'])for(const editable of [false,true]){const r=await inspect(item,b,locale,editable);actualApplications+=r.applications;interactions+=r.interactions;views++;}receipts.push({name:item.name,mode,result:b.run_result,NativeSHA256:sha(JSON.stringify(b))});contexts++;}const controls=selected?0:await corrupt(cache);console.log(JSON.stringify({passed:true,actualSources:selected?selected.size:CASES.length,sourceContexts:contexts,views,actualApplications,interactions,corruptionControls:controls,actualReflexivityAndBinaryCyclicPermutation:true,definitionAndUnregisteredControls:true,sourcePointerKeyboardSymbolPinAndExactBack:true,noInventedRegistrationIdentity:true,alternateProofNotPublished:true,ownAndAlternateWDLastClosed:true,partialLocalScopesAndKnownReuse:true,NativeUnchanged:true,actualCompilerPOSTs:options.endpoint?contexts:0,readerSHA256:sha(code),rawNativeInMemoryOnly:true,temporarySourcesRemoved:true,browserObserved:false,receipts}));}
module.exports={cases:CASES};if(require.main===module)run().catch(e=>{console.error(e);process.exitCode=1;});
