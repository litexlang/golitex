'use strict';
// Actual ring certificates; no proof-route replacement or polynomial verifier.
const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),vm=require('node:vm'),http=require('node:http'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto'),{createDOM}=require('./dom.cjs');
const ROOT=path.resolve(__dirname,'../../../..');
const CASES=[
  {
    "name": "square",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        mul(add(a,b),add(a,neg(b)))=add(mul(a,a),neg(mul(b,b)))\n",
    "result": "success"
  },
  {
    "name": "congruence",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K, h fn(x K) R:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        h(mul(add(a,b),add(a,neg(b))))=h(add(mul(a,a),neg(mul(b,b))))\n",
    "result": "success"
  },
  {
    "name": "opaque-alignment",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K, f fn(x K) K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        add(f(add(a,b)),c)=add(c,f(add(b,a)))\n",
    "result": "success"
  },
  {
    "name": "operation-alias",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K, plus fn(x,y K) K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    plus=add\n    =>:\n        plus(plus(a,b),c)=add(c,add(b,a))\n",
    "result": "success"
  },
  {
    "name": "curried-operation",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K, factory fn(t R) fn(x,y K) K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    factory(0)=add\n    =>:\n        factory(0)(a,add(b,c))=add(c,add(b,a))\n",
    "result": "success"
  },
  {
    "name": "zero-polynomial",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        mul(a,zero)=zero\n",
    "result": "success"
  },
  {
    "name": "integer-coefficient",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        add(a,a)=mul(add(one,one),a)\n",
    "result": "success"
  },
  {
    "name": "adjacent-chain",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        mul(add(a,b),add(a,neg(b)))=add(mul(a,a),neg(mul(b,b)))=add(mul(a,a),neg(mul(b,b)))\n",
    "result": "success"
  },
  {
    "name": "missing-ring",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    =>:\n        mul(add(a,b),add(a,neg(b)))=add(mul(a,a),neg(mul(b,b)))\n",
    "result": "failure"
  },
  {
    "name": "negative-ring",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    not $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        mul(add(a,b),add(a,neg(b)))=add(mul(a,a),neg(mul(b,b)))\n",
    "result": "failure"
  },
  {
    "name": "unsupported-cancellation",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    add(a,a)=add(b,b)\n    =>:\n        a=b\n",
    "result": "failure"
  },
  {
    "name": "unrelated-operation",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K, other fn(x,y K) K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        other(a,b)=other(b,a)\n",
    "result": "failure"
  },
  {
    "name": "after-rejections",
    "source": "1 = 1\n",
    "result": "success"
  },
  {
    "name": "local-prefix",
    "source": "claim:\n    ? 1 = 2\n    forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n        $comm_ring(K,add,mul,neg,zero,one)\n        =>:\n            mul(add(a,b),add(a,neg(b)))=add(mul(a,a),neg(mul(b,b)))\n",
    "result": "failure"
  },
  {
    "name": "later-reuse",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        mul(add(a,b),add(a,neg(b)))=add(mul(a,a),neg(mul(b,b)))\n\nforall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,a,b,c K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    =>:\n        mul(add(a,b),add(a,neg(b)))=add(mul(a,a),neg(mul(b,b)))\n",
    "result": "success"
  },
  {
    "name": "shift-native-two",
    "source": "have fn shifted_add(x,y R) R = x+y+1\nhave fn shifted_mul(x,y R) R = x*y+x+y\nhave fn shifted_neg(x R) R = -x-2\nby def $comm_ring(R,shifted_add,shifted_mul,shifted_neg,-1,0)\nforall a R:\n    shifted_add(a,a)=shifted_mul(2,a)\n",
    "result": "failure"
  },
  {
    "name": "native-literal-atom",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,b K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    2 $in K\n    =>:\n        mul(add(2,b),add(2,neg(b)))=add(mul(2,2),neg(mul(b,b)))\n",
    "result": "success"
  },
  {
    "name": "native-two-not-coefficient",
    "source": "forall K nonempty_set, add,mul fn(x,y K) K, neg fn(x K) K, zero,one,b K, a K:\n    $comm_ring(K,add,mul,neg,zero,one)\n    2 $in K\n    =>:\n        mul(2,a)=add(a,a)\n",
    "result": "failure"
  }
];


const options={binary:path.join(ROOT,'target/release/litex'),reader:path.join(__dirname,'../reader.js')};
if(require.main===module)for(let i=2;i<process.argv.length;i+=2){const key=process.argv[i].replace(/^--/,'');assert(['binary','reader','endpoint'].includes(key)&&process.argv[i+1]);options[key]=process.argv[i+1];}
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
 const v={...dom,root,reader,row(s){const n=root.querySelector('[data-line="'+s.line+'"]');assert(n,s.id);return n;},async hover(s,target=null,keyboard=false){target||=v.row(s).querySelector('.lr-source-code');if(keyboard)await (target||v.row(s).querySelector('.lr-line-number')).trigger('focus');else if(editable){dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await target.trigger('pointermove');for(let k=0;k<3;k++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}return root.querySelector('.lr-proof-popover');},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'Native targets, proof, scopes and publication remain unchanged');assert.equal(root.querySelectorAll('.lr-code-row').length,(root.querySelector('.lr-ide-input')?.value||(b.sources.find(source=>source.id===reader.getSelection().source)||b.sources[0]).content).split('\n').length);reader.destroy();}};return v;
}

module.exports={cases:CASES};
function applications(b,d){
 const out=[];for(const[id,n]of d.nodes){if(n.type!=='VerifyEqualitySuccess')continue;const proof=d.resolve(n.fields?.searched_proof),route=d.resolve(proof.fields?.['0']);if(proof.type!=='EqualFactSearchedProof'||proof.variant!=='ByBuiltinRewrite'||route.type!=='EqualitySearchProofByBuiltinRewrite'||route.variant!=='Ring')continue;
  const goal=d.result(n.fields.fact),target=goal.fields.fact_id.fact_id;let fact=b.facts.find(f=>f.id===target),index=0;
  if(!fact){const chain=[...d.nodes.values()].find(p=>p.type==='VerifyChainFactSuccess'&&p.fields.adjacent.some(v=>d.result(v)===n));assert(chain,'the unindexed adjacent target belongs to a retained chain');fact=b.facts.find(f=>f.id===d.result(chain.fields.fact).fields.fact_id.fact_id);index=chain.fields.adjacent.findIndex(v=>d.result(v)===n);}
  assert(fact);out.push({fact,target,index,goal,verification:n,reference:{kind:'evidence_reference',evidence_id:id},detail:d.resolve(route.fields['0'])});
 }return out;
}
async function expandRing(parent){for(let round=0;round<8;round++){const pending=parent.querySelectorAll('details').filter(n=>!n.open&&['lr-ring-notation','lr-ring-child','lr-ring-normalization','lr-ring-equalities','lr-ring-alignments'].some(c=>n.classList.contains(c)));if(!pending.length)break;for(const node of pending)await node.querySelector('summary').click();}}
function assertCard(v,app,card){const part=card?.querySelector('.lr-ring-rewrite');assert.equal(part?.dataset.status,'retained',part?.textContent||card?.textContent);assert.equal(part.dataset.targetFact,app.target);assert.equal(part.dataset.rule,'EqualitySearchProofByBuiltinRewrite::Ring');assert(!/f\d+::/.test(part.textContent));const tail=card.querySelector('.lr-atomic-wd');assert(tail&&!tail.open);assert.equal(tail.parentNode.children.at(-1),tail);return part;}
async function inspect(item,b,locale,editable){const d=records(b),apps=applications(b,d),view=mount(b,locale,editable);let interactions=0;
 const shouldHave=['square','congruence','opaque-alignment','operation-alias','curried-operation','zero-polynomial','integer-coefficient','adjacent-chain','local-prefix','later-reuse','native-literal-atom'].includes(item.name);assert.equal(apps.length,shouldHave?1:0,item.name+' must use the ordinary verifier-selected route');
 for(const app of apps){const row=view.row(app.fact),eq=row.querySelectorAll('.lr-chain-equality').find(n=>n.dataset.chainFact===app.fact.id&&Number(n.dataset.chainStep)===app.index);assert(eq);let popup=await view.hover(app.fact,eq),part=assertCard(view,app,popup);assert(!part.querySelector('.lr-ring-notation').open);if(item.name==='square'){await view.close();const whole=await view.hover(app.fact);assertCard(view,app,whole);await view.close();popup=await view.hover(app.fact,eq);part=assertCard(view,app,popup);interactions++;}if(item.name==='local-prefix'){const rejected=b.statements.find(s=>s.status==='rejected');assert.deepEqual(rejected.produced_fact_ids,[]);assert(!app.fact.scope_id.startsWith('file:'));}assert(!part.querySelectorAll('.lr-ring-normalization').some(n=>n.open));interactions++;
  await view.close();popup=await view.hover(app.fact,eq,true);part=assertCard(view,app,popup);interactions++;
  await expandRing(part);assert(part.querySelectorAll('.lr-ring-normalization-node').length>0);assert(part.textContent.includes(locale==='zh'?'整数系数':'Integer coefficients'));if(item.name==='square'||item.name==='adjacent-chain')assert(part.textContent.includes('(a)^2 − (b)^2'));if(item.name==='integer-coefficient')assert(part.textContent.includes('2 · (a)'));if(item.name==='native-literal-atom'){assert(part.textContent.includes('(2)^2 − (b)^2'));const note=part.querySelector('.lr-ring-literal-note');assert(note&&!note.closest('details'));assert(note.textContent.includes(locale==='zh'?'数值 2 属于 K':'2 is an element of K'));assert(note.textContent.includes(locale==='zh'?'环乘法':'ring multiplication'));}if(item.name==='congruence')assert.equal(part.dataset.derivation,'Congruence');if(item.name==='opaque-alignment')assert(part.querySelector('.lr-ring-alignments'));if(['operation-alias','curried-operation'].includes(item.name))assert(part.querySelector('.lr-ring-equalities'));interactions++;
  await popup.querySelector('.lr-proof-pin').click();const selection=view.reader.getSelection(),body=view.root.querySelector('.lr-detail-body'),sourceId=part.dataset.sourceFact;assertCard(view,app,body);const cite=body.querySelectorAll('.lr-fact-link').find(n=>n.dataset.fact===sourceId);assert(cite,'the actual source ring is navigable');await cite.click();assert.equal(view.reader.getSelection().fact,sourceId);await view.root.querySelector('.lr-back').click();assert.deepEqual(view.reader.getSelection(),selection);assertCard(view,app,view.root.querySelector('.lr-detail-body'));interactions+=3;await view.close();
  if(item.name==='adjacent-chain'){const other=view.row(app.fact).querySelectorAll('.lr-chain-equality').find(n=>Number(n.dataset.chainStep)===1);assert(other);const next=await view.hover(app.fact,other);assert(!next.querySelector('.lr-ring-rewrite'),'the later identity gets its own proof');interactions++;await view.close();}
 }
 if(!apps.length)assert(!view.root.querySelector('.lr-ring-rewrite'),'a missing ring route never becomes a ring application');
 if(item.name==='later-reuse'){const later=b.statements.at(-1);await view.reader.selectStatement(later.id,later.line);assert(!view.root.querySelector('.lr-detail-body .lr-ring-rewrite'),'later reuse retains its own citation route');interactions++;await view.close();}
 if(editable){const input=view.root.querySelector('.lr-ide-input');input.value+='\n';await input.trigger('input');assert(!view.root.querySelector('.lr-proof-popover'));interactions++;}
 view.done();return{views:1,applications:apps.length,interactions};
}
async function controls(){let checked=0;
 const controls=[
  ['source-fact','square',(b,d,a)=>delete a.detail.fields.source_fact],
  ['known-source','square',(b,d,a)=>delete a.detail.fields.source],
  ['negative-contract','square',(b,d,a)=>d.result(a.detail.fields.source_fact).type='NotCommRingFact'],
  ['foreign-citation','square',(b,d,a)=>d.resolve(d.resolve(d.resolve(a.detail.fields.source).fields.searched_proof).fields['0']).fields.cite_fact_id={kind:'fact_reference',fact_id:'foreign-ring'}],
  ['foreign-source-scope','square',(b,d,a)=>{const id=d.result(a.detail.fields.source_fact).fields.fact_id.fact_id;const fact=b.facts.find(f=>f.id===id);b.scopes.find(s=>s.id===fact.scope_id).parent_id='foreign-scope';}],
  ['source-argument-proof','square',(b,d,a)=>{const p=d.resolve(d.resolve(d.resolve(a.detail.fields.source).fields.searched_proof).fields['0']);p.fields.why_parameters_of_known_fact_are_equal_to_givens[0]={kind:'unavailable'};}],
  ['atoms','square',(b,d,a)=>delete a.detail.fields.atoms],
  ['membership','square',(b,d,a)=>delete d.resolve(a.detail.fields.atoms[0]).fields.membership],
  ['membership-carrier','square',(b,d,a)=>{const atom=d.resolve(a.detail.fields.atoms[0]);d.result(atom.fields.membership_fact).fields.set=atom.fields.object;}],
  ['equalities','square',(b,d,a)=>delete a.detail.fields.equalities],
  ['alignments','square',(b,d,a)=>delete a.detail.fields.atom_alignments],
  ['unknown-derivation','square',(b,d,a)=>d.resolve(a.detail.fields.derivation).variant='FutureDerivation'],
  ['target-side','square',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']);p.fields.left=d.result(a.detail.fields.source_fact).fields.carrier;}],
  ['missing-certificate','square',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']);delete p.fields.left_certificate;}],
  ['root-index','square',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']);d.resolve(p.fields.left_certificate).fields.root='999999';}],
  ['future-operation','square',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']),c=d.resolve(p.fields.left_certificate);d.resolve(d.resolve(c.fields.nodes[0]).fields.operation).variant='FutureOperation';}],
  ['atom-index','square',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']),c=d.resolve(p.fields.left_certificate);d.resolve(d.resolve(c.fields.nodes[0]).fields.operation).fields['0']='999999';}],
  ['expression-correspondence','square',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']);d.resolve(p.fields.left_expression).variant='Neg';}],
  ['polynomial-pair','square',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']),c=d.resolve(p.fields.right_certificate),node=structuredClone(d.resolve(c.fields.nodes[Number(c.fields.root)])),poly=structuredClone(d.resolve(node.fields.polynomial));poly.fields.terms[0][1]='17';node.fields.polynomial=poly;c.fields.nodes[Number(c.fields.root)]=node;}],
  ['noninteger-coefficient','square',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']),c=d.resolve(p.fields.left_certificate);d.resolve(d.resolve(c.fields.nodes[0]).fields.polynomial).fields.terms[0][1]='1/2';}],
  ['cyclic-derivation','congruence',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']);p.fields.children=[a.detail.fields.derivation];}],
  ['foreign-child','congruence',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']),known=p.fields.children.map(v=>d.resolve(v)).find(n=>n.variant==='Known'),q=d.resolve(known.fields['0']),f=d.result(q.fields.fact);f.fields.left=d.result(a.detail.fields.source_fact).fields.carrier;f.fields.right=f.fields.left;}],
  ['root-with-no-ring-step','square',(b,d,a)=>{a.detail.fields.derivation={type:'RingEqualityDerivation',variant:'Known',fields:{'0':{type:'RingEqualityRequirement',fields:{fact:a.verification.fields.fact,proof:a.reference}}}};}],
  ['empty-children','congruence',(b,d,a)=>{const p=d.resolve(d.resolve(a.detail.fields.derivation).fields['0']);p.fields.children=[];}]
 ];
 const originals=new Map();for(const[name,caseName,change]of controls){if(!originals.has(caseName))originals.set(caseName,await compile(CASES.find(c=>c.name===caseName)));const b=structuredClone(originals.get(caseName)),d=records(b),app=applications(b,d)[0];change(b,d,app);const view=mount(b,'en',true);await view.reader.selectFact(app.fact.id);const card=view.root.querySelector('.lr-detail-body .lr-ring-rewrite');assert(!card||card.dataset.status==='incomplete',name+': malformed data must not present a complete application');assert(!card?.querySelector('.lr-ring-normalization'));view.done();checked++;}
 return checked;
}
async function run(){let views=0,applicationViews=0,interactions=0;const receipts=[];
 for(const item of CASES)for(const mode of ['ordinary','registered']){const b=await compile(item,mode);for(const locale of ['zh','en'])for(const editable of [false,true]){const r=await inspect(item,b,locale,editable);views+=r.views;applicationViews+=r.applications;interactions+=r.interactions;}receipts.push({name:item.name,mode,result:b.run_result,sourceSHA256:sha(b.sources[0].content),actualRingProofs:applications(b,records(b)).length});}
 const corruptionControls=options.endpoint?0:await controls();console.log(JSON.stringify({passed:true,sourceCases:CASES.length,sourceContexts:receipts.length,views,applicationViews,interactions,corruptionControls,actualRingPolynomialCongruenceAndAtomAlignment:true,operationAliasesAndCurriedFunctions:true,zeroAndIntegerCoefficients:true,adjacentEqualitiesAndLocalFailure:true,actualCitationsAndExactBack:true,bilingualEditableReadOnlyAndKeyboard:true,sourceScopeNativeAndPublicationUnchanged:true,ownWDLastAndClosed:true,rawGraphsOnlyInMemory:true,readerSHA256:sha(code),browserObserved:false,receipts}));
}
if(require.main===module)run().catch(e=>{console.error(e);process.exitCode=1;});
