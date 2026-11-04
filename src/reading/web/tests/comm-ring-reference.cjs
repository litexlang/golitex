'use strict';
// Real total-ring interfaces, including the zero ring and guarded rejections.
const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),vm=require('node:vm'),http=require('node:http'),cp=require('node:child_process'),crypto=require('node:crypto'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),ROOT=path.resolve(__dirname,'../../../..');
const options={binary:path.join(ROOT,'target/release/litex'),reader:path.join(__dirname,'../reader.js')};
if(require.main===module)for(let i=2;i<process.argv.length;i+=2){const key=process.argv[i].replace(/^--/,'');assert(['binary','reader','endpoint'].includes(key)&&process.argv[i+1]);options[key]=process.argv[i+1];}
const catalogue=JSON.parse(fs.readFileSync(path.join(__dirname,'../../language_reference.json'),'utf8')),reference=catalogue.entries.comm_ring;
assert(reference,'the card has one source-owned catalogue entry');
const real=reference.example,zero='have fn zero_add(x, y {0}) {0} = 0\nhave fn zero_mul(x, y {0}) {0} = 0\nhave fn zero_neg(x {0}) {0} = 0\nby def $comm_ring({0}, zero_add, zero_mul, zero_neg, 0, 0)',shifted='have fn shifted_add(x, y R) R = x + y + 1\nhave fn shifted_mul(x, y R) R = x * y + x + y\nhave fn shifted_neg(x R) R = -x - 2\nby def $comm_ring(R, shifted_add, shifted_mul, shifted_neg, -1, 0)',partial=real+'\nhave fn partial_add(x, y R: x > 0) R = x + y\n';
const CASES=[
 {name:'displayed-real-example',source:real,result:'success'},
 {name:'zero-ring',source:zero,result:'success'},
 {name:'shifted-identities',source:shifted,result:'success'},
 {name:'abstract-ring-use',file:'examples/proof_nodes/equal/by_builtin_rewrite/comm_ring_polynomial.lit',result:'success'},
 {name:'negative-local-premise',source:'forall K nonempty_set, add, mul fn(x, y K) K, neg fn(x K) K, zero, one K:\n    not $comm_ring(K, add, mul, neg, zero, one)\n    =>:\n        not $comm_ring(K, add, mul, neg, zero, one)',result:'success'},
 {name:'guarded-operation-positive',source:partial+'by def $comm_ring(R, partial_add, ring_mul, ring_neg, 0, 1)',result:'failure'},
 {name:'guarded-operation-negative',source:partial+'not $comm_ring(R, partial_add, ring_mul, ring_neg, 0, 1)',result:'failure'},
 {name:'missing-argument',source:real+'\nby def $comm_ring(R, ring_add, ring_mul, ring_neg, 0)',result:'failure'}
];
const readerCode=fs.readFileSync(options.reader,'utf8'),sha=s=>crypto.createHash('sha256').update(s).digest('hex');
function fnv(s){let n=0xcbf29ce484222325n;for(const b of Buffer.from(s))n=((n^BigInt(b))*0x100000001b3n)&0xffffffffffffffffn;return'fnv1a64:'+n.toString(16).padStart(16,'0');}
function post(payload){const url=new URL('/api/reading/build',options.endpoint);assert.equal(url.hostname,'127.0.0.1');return new Promise((resolve,reject)=>{const req=http.request(url,{method:'POST',headers:{'Content-Type':'application/json','Origin':url.origin}},res=>{const chunks=[];res.on('data',c=>chunks.push(c));res.on('end',()=>{try{assert.equal(res.statusCode,200);resolve(Buffer.concat(chunks).toString());}catch(e){reject(e);}});});req.on('error',reject);req.end(JSON.stringify(payload));});}
async function compile(item,mode){
 const source=item.source||fs.readFileSync(path.join(ROOT,item.file),'utf8');let raw;
 if(options.endpoint){const files=[{path:'candidate.lit',content:source}];if(mode==='registered')files.push({path:'litex.config',content:'[export]\nf0 = "./candidate.lit"\n'});raw=await post({language:'en',strict:true,entry:{kind:'file',path:'candidate.lit'},files});}
 else{const dir=fs.mkdtempSync(path.join(os.tmpdir(),'litex-comm-ring-reference-')),file=path.join(dir,'candidate.lit'),config=path.join(dir,'litex.config');try{fs.writeFileSync(file,source);if(mode==='registered')fs.writeFileSync(config,'[export]\nf0 = "./candidate.lit"\n');const r=cp.spawnSync(path.resolve(options.binary),['-reading','-json','-strict','-lang','en','-f',file],{encoding:'utf8',maxBuffer:32*1024*1024,timeout:60000});assert(!r.error,item.name+': '+r.error);assert.equal(r.status,item.result==='success'?0:1,item.name+': '+r.stderr);raw=r.stdout;}finally{if(fs.existsSync(config))fs.unlinkSync(config);if(fs.existsSync(file))fs.unlinkSync(file);fs.rmdirSync(dir);}}
 const b=JSON.parse(raw);assert.equal(b.run_result,item.result,item.name);assert.equal(b.execution_policy.strict,true);
 if(item.name.startsWith('guarded-operation-')){const rejected=b.statements.find(s=>s.status==='rejected');assert(rejected);assert.equal(rejected.failure?.category,'well_defined');assert(rejected.failure.obligation.includes('partial_add $in fn ('));assert.deepEqual(rejected.produced_fact_ids,[]);assert.deepEqual(rejected.inferred_fact_ids,[]);assert(!b.facts.some(f=>f.role==='verified'&&f.producer_statement_id===rejected.id));}
 if(item.name==='missing-argument')assert(b.diagnostics.some(d=>d.phase==='parse'&&d.summary==='`comm_ring` requires 6 arguments, got 5'));
 assert.deepEqual(b.sources.map(s=>s.content),[source]);assert.equal(b.sources[0].digest,fnv(source));const copy={...b},id=copy.bundle_id;delete copy.bundle_id;assert.equal(id,fnv(JSON.stringify(copy)));return b;
}
function mount(b,locale,editable){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(b),timers=new Map();let serial=0;
 vm.runInContext(readerCode,vm.createContext({...dom,console,URL,TextEncoder,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:b,locale,...(editable?{onCheck:async()=>b}:{})});
 async function flush(){for(let round=0;round<3;round++)for(const[id,fn]of[...timers])if(timers.has(id)){timers.delete(id);await fn();}}
 return {...dom,root,reader,async hover(token,keyboard=false){if(keyboard)await token.trigger('focus');else if(editable){dom.document.elementFromPoint=()=>token;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await token.trigger('pointermove');await flush();const card=root.querySelector('.lr-proof-symbol:not([hidden])')||root.querySelector('.lr-token-help');assert(card,'the reserved predicate has source-adjacent help');return card;},async close(){await root.trigger('keydown',{key:'Escape'});},done(){assert.equal(JSON.stringify(b),before,'reference interactions preserve actual proof, source, scope and publication');assert.equal(root.querySelectorAll('.lr-code-row').length,(root.querySelector('.lr-ide-input')?.value||b.sources[0].content).split('\n').length);reader.destroy();}};
}
function checkCard(card,locale){
 assert.equal(card.querySelector('.lr-reference-kind')?.textContent,locale==='zh'?'内置谓词':'Builtin predicate');
 assert.equal(card.querySelector('.lr-reference-syntax')?.textContent,'$comm_ring(K, add, mul, neg, zero, one)');
 assert.equal(card.querySelector('.lr-reference-example')?.textContent,real,'the visible example is the exact strictly checked input');
 const notes=card.querySelector('.lr-reference-notes')?.textContent;assert(notes);assert(notes.includes('K × K → K'));assert(notes.includes('K → K'));assert(notes.includes('zero, one ∈ K')||notes.includes('zero、one ∈ K'));assert(notes.includes('zero=one'));assert(notes.includes('not $comm_ring(...)'));
 assert(notes.includes('mul(x,add(y,z))=add(mul(x,y),mul(x,z))'));assert(notes.includes(locale==='zh'?'全函数':'total functions'));assert(notes.includes(locale==='zh'?'非空集合':'nonempty set'));assert(notes.includes(locale==='zh'?'不要求非零元可逆':'inverses of nonzero elements are not required'));
}
async function inspect(item,b,locale,editable){
 const view=mount(b,locale,editable),tokens=view.root.querySelectorAll('[data-keyword="comm_ring"]');assert(tokens.length,item.name);const token=tokens.at(-1);assert.equal(token.dataset.syntax,'predicate');
 checkCard(await view.hover(token),locale);await view.close();checkCard(await view.hover(token,true),locale);await view.close();
 await token.click();assert.equal(view.reader.getSelection().keyword,'comm_ring');checkCard(view.root.querySelector('.lr-detail-body'),locale);await view.close();
 if(editable){const input=view.root.querySelector('.lr-ide-input');input.value+='\n';await input.trigger('input');assert(!view.root.querySelector('.lr-proof-popover'));assert(!view.root.querySelector('.lr-token-help'));}
 view.done();return 3+(editable?1:0);
}
async function run(){
 let views=0,interactions=0;const cases=[];
 for(const item of CASES)for(const mode of ['ordinary','registered']){const b=await compile(item,mode);for(const locale of ['zh','en'])for(const editable of [false,true]){interactions+=await inspect(item,b,locale,editable);views++;}cases.push({name:item.name,mode,result:b.run_result,sourceSHA256:sha(b.sources[0].content)});}
 console.log(JSON.stringify({passed:true,sourceCases:CASES.length,sourceContexts:cases.length,views,interactions,bilingualEditableAndReadOnly:true,exactSixArgumentSignature:true,realZeroAndShiftedRings:true,positiveAndNegativeTotalDomainRejections:true,exactDisplayedExampleStrictlyChecked:true,hoverFocusClickAndEditInvalidation:true,sourceAndNativeEvidenceUnchanged:true,rawGraphsOnlyInMemory:true,readerSHA256:sha(readerCode),browserObserved:false,cases}));
}
if(require.main===module)run().catch(error=>{console.error(error);process.exitCode=1;});
module.exports={cases:CASES};
