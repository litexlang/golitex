'use strict';
// Actual failed function definitions,without reconstructed scopes or branches.
const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),vm=require('node:vm'),http=require('node:http'),cp=require('node:child_process'),assert=require('node:assert/strict'),crypto=require('node:crypto'),{createDOM}=require('./dom.cjs');
const ROOT=path.resolve(__dirname,'../../../..');
const CASES=[
  {
    "name": "have_fn_equal_stmt-ill-defined-function-body",
    "file": "examples/test_statements/negative/have_fn_equal_stmt/ill-defined-function-body.lit",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "AnonymousFnWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "Body",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "have_fn_equal_stmt-wrong-call-arity",
    "file": "examples/test_statements/negative/have_fn_equal_stmt/wrong-call-arity.lit",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "",
    "positive": true,
    "callError": true,
    "acceptedCount": 1,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
  },
  {
    "name": "have_fn_equal_stmt-wrong-codomain",
    "file": "examples/test_statements/negative/have_fn_equal_stmt/wrong-codomain.lit",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "AnonymousFnWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "BodyInRetSet",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "have_fn_equal_case_by_case_stmt-missing-case",
    "file": "examples/test_statements/negative/have_fn_equal_case_by_case_stmt/missing-case.lit",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualCaseByCaseStmt",
    "route": "cases",
    "algorithm": false,
    "stage": "Coverage",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "have_fn_equal_case_by_case_stmt-wrong-case-codomain",
    "file": "examples/test_statements/negative/have_fn_equal_case_by_case_stmt/wrong-case-codomain.lit",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualCaseByCaseStmt",
    "route": "cases",
    "algorithm": false,
    "stage": "CaseBodyInRetSet",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      0
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "have_fn_by_induc_stmt-bad-base-carrier",
    "file": "examples/test_statements/negative/have_fn_by_induc_stmt/bad-base-carrier.lit",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "CaseBodyInRetSet",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      0
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "have_fn_by_induc_stmt-nondecreasing-recursion",
    "file": "examples/test_statements/negative/have_fn_by_induc_stmt/nondecreasing-recursion.lit",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "CaseBodyWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      1
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "have_fn_by_forall_exist_unique_stmt-false-unique-natural",
    "file": "examples/test_statements/negative/have_fn_by_forall_exist_unique_stmt/false-unique-natural.lit",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByForallExistUniqueStmt",
    "route": "unique",
    "algorithm": false,
    "stage": "SourceForall",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "have_fn_by_forall_exist_unique_stmt-ordinary-existence-is-insufficient",
    "file": "examples/test_statements/negative/have_fn_by_forall_exist_unique_stmt/ordinary-existence-is-insufficient.lit",
    "result": "failure",
    "parse": true
  },
  {
    "name": "def_algo_by_cases_stmt-bad-algorithm-result",
    "file": "examples/test_statements/negative/def_algo_by_cases_stmt/bad-algorithm-result.lit",
    "result": "failure",
    "parse": false,
    "leaf": "DefAlgoByCasesStmt",
    "route": "algo-cases",
    "algorithm": true,
    "stage": "CaseBodyInRetSet",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      0
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "def_algo_by_cases_stmt-nonexhaustive-algorithm",
    "file": "examples/test_statements/negative/def_algo_by_cases_stmt/nonexhaustive-algorithm.lit",
    "result": "failure",
    "parse": false,
    "leaf": "DefAlgoByCasesStmt",
    "route": "algo-cases",
    "algorithm": true,
    "stage": "Coverage",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "def_algo_by_induc_stmt-nondecreasing-algorithm-recursion",
    "file": "examples/test_statements/negative/def_algo_by_induc_stmt/nondecreasing-algorithm-recursion.lit",
    "result": "failure",
    "parse": false,
    "leaf": "DefAlgoByInducStmt",
    "route": "algo-recursive",
    "algorithm": true,
    "stage": "CaseBodyWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      1
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "def_algo_by_induc_stmt-wrong-base-value",
    "file": "examples/test_statements/negative/def_algo_by_induc_stmt/wrong-base-value.lit",
    "result": "failure",
    "parse": false,
    "leaf": "DefAlgoByInducStmt",
    "route": "algo-recursive",
    "algorithm": true,
    "stage": "CaseBodyInRetSet",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      0
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "formula-body-failure",
    "source": "have fn reading_formula_repair(x R) R = 1 / x\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "AnonymousFnWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "Body",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "formula-body-repair",
    "source": "have fn reading_formula_repair(x R: x != 0) R = 1 / x\n",
    "result": "success",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "",
    "positive": true,
    "callError": false,
    "acceptedCount": 1,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
  },
  {
    "name": "formula-parameter-wd",
    "source": "have fn reading_bad_domain(x (1 / 0)) R = 1\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "AnonymousFnWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "ParamType",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": true
  },
  {
    "name": "formula-return-wd",
    "source": "have fn reading_bad_return(x R) (1 / 0) = 1\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "AnonymousFnWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "RetSet",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": true
  },
  {
    "name": "formula-condition-wd",
    "source": "have fn reading_bad_condition(x R: 1 / 0 > 0) R = 1\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "AnonymousFnWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "DomFact",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": true
  },
  {
    "name": "cases-overlap",
    "source": "have fn reading_overlap(x R) N by cases:\n    case x >= 0: 0\n    case x <= 0: 1\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualCaseByCaseStmt",
    "route": "cases",
    "algorithm": false,
    "stage": "Disjoint",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": [
      0,
      1
    ],
    "wd": false,
    "zero": false
  },
  {
    "name": "cases-body-wd",
    "source": "have fn reading_case_wd(x R) R by cases:\n    case x >= 0: 1 / x\n    case x < 0: 0\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualCaseByCaseStmt",
    "route": "cases",
    "algorithm": false,
    "stage": "CaseBodyWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      0
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "cases-interface-wd",
    "source": "have fn reading_case_interface(x R) (1 / 0) by cases:\n    case x = x: 0\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualCaseByCaseStmt",
    "route": "cases",
    "algorithm": false,
    "stage": "FnSetWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": true
  },
  {
    "name": "recursive-measure-integer",
    "source": "have fn reading_measure_integer(n R) R by induc n from 0:\n    case n = n: 0\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "MeasureNotInteger",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "recursive-lower-integer",
    "source": "have fn reading_lower_integer(n N) N by induc n from 0.5:\n    case n = n: 0\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "LowerBoundNotInteger",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "recursive-measure-bound",
    "source": "have fn reading_measure_bound(n Z) Z by induc n from 0:\n    case n = n: 0\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "MeasureBelowLower",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "recursive-measure-wd",
    "source": "have fn reading_measure_wd(n N) N by induc 1 / 0 from 0:\n    case n = n: 0\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "MeasureWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": true
  },
  {
    "name": "recursive-lower-wd",
    "source": "have fn reading_lower_wd(n N) N by induc n from 1 / 0:\n    case n = n: 0\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "LowerBoundWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": true
  },
  {
    "name": "recursive-nested-return",
    "source": "have fn reading_nested_bad(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1:\n        case n = 1: -1\n        case n != 1: reading_nested_bad(n - 1)\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "CaseBodyInRetSet",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      1,
      0
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "algo-nested-return",
    "source": "algo reading_nested_algo_bad(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1:\n        case n = 1: -1\n        case n != 1: reading_nested_algo_bad(n - 1)\n",
    "result": "failure",
    "parse": false,
    "leaf": "DefAlgoByInducStmt",
    "route": "algo-recursive",
    "algorithm": true,
    "stage": "CaseBodyInRetSet",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [
      1,
      0
    ],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "recursive-overlap",
    "source": "have fn reading_recursive_overlap(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 0: 1\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "Disjoint",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": [
      0,
      1
    ],
    "wd": false,
    "zero": false
  },
  {
    "name": "recursive-coverage",
    "source": "have fn reading_recursive_missing(n N) N by induc n from 0:\n    case n = 0: 0\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "Coverage",
    "positive": false,
    "callError": false,
    "acceptedCount": 0,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "cases-positive",
    "source": "have fn reading_case_good(x R) N by cases:\n    case x = 0: 0\n    case x != 0: 1\n",
    "result": "success",
    "parse": false,
    "leaf": "HaveFnEqualCaseByCaseStmt",
    "route": "cases",
    "algorithm": false,
    "stage": "",
    "positive": true,
    "callError": false,
    "acceptedCount": 1,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
  },
  {
    "name": "recursive-positive",
    "source": "have fn reading_recursive_good(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: n\n",
    "result": "success",
    "parse": false,
    "leaf": "HaveFnByInducStmt",
    "route": "recursive",
    "algorithm": false,
    "stage": "",
    "positive": true,
    "callError": false,
    "acceptedCount": 1,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
  },
  {
    "name": "algo-cases-positive",
    "source": "algo reading_case_algo_good(x R) N by cases:\n    case x = 0: 0\n    case x != 0: 1\n",
    "result": "success",
    "parse": false,
    "leaf": "DefAlgoByCasesStmt",
    "route": "algo-cases",
    "algorithm": true,
    "stage": "",
    "positive": true,
    "callError": false,
    "acceptedCount": 1,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
  },
  {
    "name": "algo-recursive-positive",
    "source": "algo reading_recursive_algo_good(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: n\n",
    "result": "success",
    "parse": false,
    "leaf": "DefAlgoByInducStmt",
    "route": "algo-recursive",
    "algorithm": true,
    "stage": "",
    "positive": true,
    "callError": false,
    "acceptedCount": 1,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
  },
  {
    "name": "unique-positive",
    "source": "prop reading_unique_rel(x, y R):\n    y = x\nclaim:\n    ? forall x R:\n        exist! y R st {$reading_unique_rel(x, y)}\n    witness exist! y R st {$reading_unique_rel(x, y)} from x:\n        by def $reading_unique_rel(x, x)\nhave fn reading_unique_good by exist!:\n    ? forall x R:\n        exist! y R st {$reading_unique_rel(x, y)}\n",
    "result": "success",
    "parse": false,
    "leaf": "HaveFnByForallExistUniqueStmt",
    "route": "unique",
    "algorithm": false,
    "stage": "",
    "positive": true,
    "callError": false,
    "acceptedCount": 1,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
  },
  {
    "name": "local-partial",
    "source": "claim:\n    ? 1 = 1\n    have fn reading_local_good(x R) R = x\n    have fn reading_local_bad(x R) N = -1\n",
    "result": "failure",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "AnonymousFnWellDefined",
    "positive": false,
    "callError": false,
    "acceptedCount": 1,
    "substage": "BodyInRetSet",
    "path": [],
    "pair": null,
    "wd": true,
    "zero": false
  },
  {
    "name": "repeated-formula",
    "source": "by enumerate finite_set:\n    ? forall reading_function_k {0, 1}:\n        reading_function_k = reading_function_k\n    have fn reading_repeated_formula(x R) R = x\n",
    "result": "success",
    "parse": false,
    "leaf": "HaveFnEqualStmt",
    "route": "formula",
    "algorithm": false,
    "stage": "",
    "positive": true,
    "callError": false,
    "acceptedCount": 2,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
  },
  {
    "name": "repeated-algorithm",
    "source": "by enumerate finite_set:\n    ? forall reading_algorithm_k {0, 1}:\n        reading_algorithm_k = reading_algorithm_k\n    algo reading_repeated_algorithm(x R) N by cases:\n        case x = x: 0\n",
    "result": "success",
    "parse": false,
    "leaf": "DefAlgoByCasesStmt",
    "route": "algo-cases",
    "algorithm": true,
    "stage": "",
    "positive": true,
    "callError": false,
    "acceptedCount": 2,
    "substage": "",
    "path": [],
    "pair": null,
    "wd": false,
    "zero": false
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
async function inspect(item,b,locale,editable){const v=mount(b,locale,editable);let interactions=0;
 if(item.parse){assert(b.diagnostics.some(d=>d.phase==='parse'));assert(!b.statements.some(s=>s.status==='rejected'&&s.statement_kind.startsWith('Definition.')));assert(!v.root.querySelector('.lr-function-definition-failure'));v.done();return{views:0,interactions};}
 const selected=b.statements.filter(s=>s.statement_kind==='Definition.'+item.leaf&&['accepted','rejected'].includes(s.status));assert(selected.length,item.name);assert.equal(selected.filter(s=>s.status==='accepted').length,item.acceptedCount);
 for(const s of selected){let card=await v.hover(s);assert(card,item.name);if(s.status==='accepted'){await v.reader.selectStatement(s.id);assert.equal(v.reader.getSelection().statement,s.id);const part=v.root.querySelector('.lr-detail-body .lr-function-definition');assert(part,item.name);assert(!v.root.querySelector('.lr-detail-body .lr-function-definition-failure'));assert(s.produced_fact_ids.length);await v.close();interactions+=2;continue;}
  const part=card.querySelector('.lr-function-definition-failure');assert.equal(part?.dataset.status,'stage-retained',item.name+': stage='+part?.dataset.stage+' '+card.textContent);assert.equal(part.dataset.statement,s.id);assert.equal(part.dataset.route,item.route.replace('algo-',''));assert.equal(part.dataset.algorithm,String(item.algorithm));assert.equal(part.dataset.stage,item.stage);assert.equal(part.dataset.substage,item.substage);assert.equal(s.produced_fact_ids.length,0);assert.equal(s.inferred_fact_ids.length,0);assert(!v.row(s).querySelector('.lr-inference-toggle'));
  if(item.path.length)assert.equal(part.querySelector('.lr-function-failed-branch').textContent,(locale==='zh'?'分支 · ':'Branch · ')+item.path.map(i=>i+1).join(' → '));if(item.pair){assert(part.querySelector('.lr-function-disjoint-pair'));assert(!part.querySelector('.lr-function-definition-failed-goal,.lr-atomic-wd'),'the disjoint indices do not acquire a missing failed proof or WD');}
  const goal=part.querySelector('.lr-function-definition-failed-goal');if(goal){assert(goal.dataset.fact);assert(!goal.querySelector('.lr-fact-link'));assert(!/f\d+::/.test(goal.textContent));}
  const tail=part.querySelector('.lr-atomic-wd');if(item.wd){assert(tail&&!tail.open,item.name+': retained WD final and folded');assert.equal(part.children.at(-1),tail);await tail.querySelector('summary').click();if(item.zero)assert(tail.querySelector('.lr-wd-unproved-conditions')?.textContent.includes('0 ≠ 0'),tail.textContent);interactions++;}else assert(!tail);
  await card.querySelector('.lr-proof-pin').click();assert.equal(v.reader.getSelection().statement,s.id);assert(v.root.querySelector('.lr-detail-body .lr-function-definition-failure'));await v.close();assert((await v.hover(s,null,true)).querySelector('.lr-function-definition-failure'));await v.close();const keyword=v.row(s).querySelector('[data-keyword]');if(keyword){card=await v.hover(s,keyword);assert.equal(card.querySelector('.lr-function-definition-failure')?.dataset.statement,s.id);await v.close();}interactions+=3;
 }
 if(item.callError){const failed=b.statements.find(s=>s.status==='rejected'&&s.statement_kind==='Fact');assert(failed);const card=await v.hover(failed);assert(card);assert(!card.querySelector('.lr-function-definition-failure'),'a wrong later call does not turn its accepted definition into a failed definition');await v.close();interactions++;}
 if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert(!v.root.querySelector('.lr-function-definition-failure,.lr-proof-popover,.lr-diagnostic-point'));}v.done();return{views:selected.length,interactions};
}
async function corruptionControls(){let checked=0;for(const control of ['root-type','dispatcher','result','failure-type','future-stage','payload-missing','payload-type','source-span','source-line','scope','origin','canonical','tokens','publication','inference','legacy']){
 const item=CASES.find(c=>c.name==='have_fn_equal_stmt-ill-defined-function-body'),b=await compile(item),d=records(b),s=b.statements.find(s=>s.status==='rejected'),root=d.resolve(s.evidence),dispatch=d.resolve(root.fields['0']),result=d.resolve(dispatch.fields['0']),failure=d.resolve(result.fields['0']);
 if(control==='root-type')root.type='FutureExecution';if(control==='dispatcher')dispatch.variant='HaveFnByInduc';if(control==='result')result.variant='Success';if(control==='failure-type')failure.type='FutureDefinitionFailure';if(control==='future-stage')failure.variant='FutureStage';if(control==='payload-missing')delete failure.fields['0'];if(control==='payload-type')d.resolve(failure.fields['0']).type='FutureObjectCheck';if(control==='source-span')s.start_byte++;if(control==='source-line')s.line++;if(control==='scope')s.scope_id='foreign';if(control==='origin')s.origin='generated';if(control==='canonical')s.source_statement_id='foreign';if(control==='tokens')b.sources[0].tokens[0].text='let';if(control==='publication')s.produced_fact_ids=['foreign'];if(control==='inference')s.inferred_fact_ids=['foreign'];if(control==='legacy')delete s.evidence;
 const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-function-definition-failure');if(part){assert.equal(part.dataset.status,'incomplete',control);assert(!part.querySelector('.lr-function-definition-failed-goal,.lr-atomic-wd'));}v.done();checked++;
 }
 for(const[name,controls]of [['have_fn_equal_case_by_case_stmt-wrong-case-codomain',['index-missing','proof-missing','goal-id','goal-location','goal-family']],['recursive-nested-return',['nested-index','nested-type','cycle']],['cases-overlap',['pair-index','pair-order']],['have_fn_equal_stmt-wrong-codomain',['reason-type','reason-family','anonymous-type','anonymous-stage','failed-goal']],['def_algo_by_cases_stmt-bad-algorithm-result',['algorithm-stage','inner-type']],['cases-interface-wd',['interface-object']]])for(const control of controls){
  const item=CASES.find(c=>c.name===name),b=await compile(item),d=records(b),s=b.statements.find(s=>s.status==='rejected'&&s.statement_kind==='Definition.'+item.leaf);let n=d.resolve(s.evidence);for(let i=0;i<3;i++)n=d.resolve(n.fields['0']);
  if(control==='index-missing')delete n.fields['0'];if(control==='proof-missing')delete n.fields['1'];if(control==='goal-id')delete d.result(d.result(n.fields['1']).fields.fact).fields.fact_id;if(control==='goal-family')d.result(d.result(n.fields['1']).fields.fact).type='EqualFact';if(control==='goal-location')d.result(d.result(n.fields['1']).fields.fact).fields.line_file={source_id:'foreign',line:1};if(control==='nested-index')delete n.fields.index;if(control==='nested-type')d.resolve(n.fields.failed).type='FutureNestedCase';if(control==='cycle')n.fields.failed=s.evidence;if(control==='pair-index')delete n.fields.i;if(control==='pair-order')n.fields.j=n.fields.i;
  if(['reason-type','reason-family','anonymous-type','anonymous-stage','failed-goal'].includes(control)){const object=d.resolve(n.fields['0']),reason=d.resolve(object.fields.reason),family=d.resolve(reason.fields['0']),anonymous=d.resolve(family.fields['0']);if(control==='reason-type')reason.type='FutureFailure';if(control==='reason-family')reason.variant='Literal';if(control==='anonymous-type')anonymous.type='FutureAnonymousFailure';if(control==='anonymous-stage')anonymous.variant='FutureStage';if(control==='failed-goal')delete d.result(d.result(anonymous.fields.failed).fields.fact).fields.fact_id;}
  if(control==='interface-object'){const root=d.resolve(n.fields['0']);d.resolve(root.fields.obj).variant='Literal';d.resolve(root.fields.reason).variant='Literal';}if(control==='algorithm-stage')n.variant='FutureAlgorithmStage';if(control==='inner-type')d.resolve(n.fields['0']).type='FutureFunctionFailure';
  const v=mount(b,'en',false);await v.reader.selectStatement(s.id);const part=v.root.querySelector('.lr-function-definition-failure');assert(part);assert.equal(part.dataset.status,'incomplete',name+':'+control);assert(!part.querySelector('.lr-function-definition-failed-goal,.lr-atomic-wd'));v.done();checked++;
 }
 return checked;
}
async function run(){let contexts=0,views=0,interactions=0;const receipts=[],selection=options.cases?new Set(options.cases.split(',')):null;
 for(const item of CASES.filter(c=>!selection||selection.has(c.name)))for(const mode of ['ordinary','registered']){const b=await compile(item,mode);for(const locale of ['zh','en'])for(const editable of [false,true]){const r=await inspect(item,b,locale,editable);views+=r.views;interactions+=r.interactions;}receipts.push({name:item.name,mode,result:b.run_result,NativeSHA256:sha(JSON.stringify(b))});contexts++;}
 const controls=selection?0:await corruptionControls();console.log(JSON.stringify({passed:true,sourceContexts:contexts,views,interactions,corruptionControls:controls,actualObservedStages:[...new Set(CASES.filter(c=>!c.positive&&!c.parse&&(!selection||selection.has(c.name))).map(c=>c.route+'.'+c.stage+(c.substage?'.'+c.substage:'')))],bilingualEditableReadOnly:true,actualBranchPathAndAlgorithmWrapper:true,failedGoalsUnpublished:true,missingHistoriesNotInvented:true,acceptedDefinitionSurvivesWrongCall:true,WDLastAndClosedWhenRetained:true,NativeUnchanged:true,actualCompilerPOSTs:options.endpoint?contexts+controls:0,readerSHA256:sha(code),rawNativeInMemoryOnly:true,temporarySourceFilesRemoved:true,browserObserved:false,receipts}));
}
module.exports={cases:CASES};if(require.main===module)run().catch(e=>{console.error(e);process.exitCode=1;});
