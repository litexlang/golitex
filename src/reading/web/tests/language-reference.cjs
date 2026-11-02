'use strict';
// Public component behavior with real CLI-exported source and token spans.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node language-reference.cjs <glossary-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,name+'.json'),'utf8'));
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0;
 vm.runInContext(code,vm.createContext({...dom,console,TextEncoder,URL,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>bundle});
 async function flush(){for(let round=0;round<3;round++)for(const [id,fn] of [...timers])if(timers.has(id)){timers.delete(id);fn();}}
 return {...dom,root,reader,row(kind){const statement=bundle.statements.find(s=>s.statement_kind?.split('.').at(-1)===kind);assert(statement,kind);return root.querySelector('[data-line="'+statement.line+'"]');},async hover(target,focus=false){assert(target);if(focus)await target.trigger('focus');else{dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}await flush();const card=root.querySelector('.lr-proof-symbol:not([hidden])')||root.querySelector('.lr-token-help');assert(card,target.textContent);return card;},done(){assert.equal(JSON.stringify(bundle),before,'glossary display leaves execution evidence unchanged');reader.destroy();}};
}
async function run(){
 const cases=[
  ['glossary-by-thm','ByThmStmt','by thm','选择并建立其中一个原子结论','one selected atomic conclusion'],
  ['glossary-have-equal','HaveObjEqualStmt','have','在声明域内用等式定义对象','by equality within a declared domain'],
  ['glossary-have-arbitrary','HaveObjInNonemptySetStmt','have','已知非空','known nonempty'],
  ['glossary-function-cases','HaveFnEqualCaseByCaseStmt','have fn','穷尽定义域','covering its domain'],
  ['glossary-algorithm','DefAlgoByCasesStmt','algo','可执行分支','executable cases'],
  ['glossary-preimage','HaveByPreimageStmt','have by fn_preimage','指定函数值','specified function value'],
  ['glossary-release-tuple','ReleaseTupleDefStmt','release tuple def','坐标及维数','coordinates and dimension'],
  ['glossary-enumerate','ByEnumerateFiniteSetStmt','by enumerate finite_set','逐个验证有限集合','checking each element'],
  ['glossary-extension','ByExtensionStmt','by extension','相互包含','mutual inclusion'],
  ['glossary-cases','ByCasesStmt','by cases','穷尽可能性','exhaustive case split'],
 ];
 for(const locale of ['zh','en']){
  for(const [name,kind,keyword,zh,en] of cases){const view=mount(fixture(name),locale),row=view.row(kind),token=row.querySelector('[data-keyword="'+keyword+'"]');assert(token,keyword);const card=await view.hover(token);assert(card.textContent.includes(locale==='zh'?zh:en),card.textContent);assert(card.querySelector('.lr-reference-notes'));assert(!view.root.querySelector('.lr-json-pane,.lr-json-toggle'));if(kind==='HaveFnEqualCaseByCaseStmt'){await token.click();assert(view.root.querySelector('.lr-detail-body').textContent.includes(locale==='zh'?zh:en),'click and hover use the same statement-specific card');assert.equal(view.reader.getSelection().keyword,'have fn','public keyword selection retains its syntax identity');}view.done();}
  const view=mount(fixture('glossary-injective'),locale),row=view.row('ByDefStmt'),token=row.querySelectorAll('[data-syntax]').find(t=>t.textContent==='injective'),card=await view.hover(token);assert(card.textContent.includes('$injective(A, B, f)'));assert(card.textContent.includes(locale==='zh'?'单射':'injective from A to B'));view.done();
  const definitions=mount(fixture('glossary-by-thm'),locale),bydef=definitions.row('ByDefStmt'),keyword=bydef.querySelector('[data-keyword="by def"]'),reference=await definitions.hover(keyword,true);assert(reference.querySelector('.lr-reference-example'),'the existing checked example survives statement-specific documentation');assert(reference.textContent.includes('nonnegative(3)'));definitions.done();
  const theorem=mount(fixture('glossary-by-thm'),locale),theoremToken=theorem.row('ByThmStmt').querySelector('[data-keyword="by thm"]'),theoremCard=await theorem.hover(theoremToken,true);assert(theoremCard.querySelector('.lr-reference-example').textContent.includes('by thm squares_are_nonnegative(3)'));assert(theoremCard.querySelector('.lr-reference-hint'));await theoremToken.click();const walkthrough=theorem.root.querySelector('.lr-detail-body .lr-reference-walkthrough');assert(walkthrough);assert.equal(walkthrough.querySelectorAll('dt').length,3);assert(walkthrough.textContent.includes('x = 3'));assert(walkthrough.textContent.includes('release thm'));theorem.done();
  const sets=mount(fixture('glossary-have-equal'),locale),r=sets.root.querySelectorAll('[data-symbol]').find(t=>t.textContent==='R'),meaning=await sets.hover(r);assert(meaning.textContent.includes(locale==='zh'?'实数集':'Real numbers'));assert(meaning.querySelector('.lr-reference-notes'),'resolved builtin-set identity receives the full card');sets.done();
  const numbers=mount(fixture('glossary-by-thm'),locale),number=numbers.row('ByDefStmt').querySelector('[data-syntax="number"]'),numeric=await numbers.hover(number);assert(numeric.textContent.includes(locale==='zh'?'精确数':'exact number'));numbers.done();
  const unicode=mount(fixture('glossary-unicode'),locale);
  const authored=JSON.parse(fs.readFileSync(path.join(__dirname,'../../language_reference.json'),'utf8')).entries;
  for(const [spelling,name] of [['ℕ+','N+'],['ℤ+','Z+'],['ℚ+','Q+'],['ℝ+','R+'],['ℤ-','Z-'],['ℚ-','Q-'],['ℝ-','R-'],['ℤ*','Z*'],['ℚ*','Q*'],['ℝ*','R*'],['ℂ*','C*']]){
   const token=unicode.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spelling),card=await unicode.hover(token);assert(card.querySelector('.lr-reference-notes'),spelling);assert(card.textContent.includes(authored[name].summary[locale]),card.textContent);
  }
  for(const [spelling,needle] of [['ℝ+',locale==='zh'?'正实数':'Positive real'],['∀',locale==='zh'?'任意对象':'every object'],['∈',locale==='zh'?'元素':'element'],['∃!',locale==='zh'?'唯一性':'uniqueness']]){
   const token=unicode.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spelling),card=await unicode.hover(token);assert(card.querySelector('.lr-reference-notes'),spelling);assert(card.textContent.toLowerCase().includes(needle.toLowerCase()),card.textContent);
  }
  for(const [spelling,syntax,needle] of [['∪','A ∪ B','x ∈ A ∨ x ∈ B'],['∩','A ∩ B','x ∈ A ∧ x ∈ B'],['×','A × B','p(1)']]){
   const token=unicode.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spelling);assert.equal(token.dataset.syntax,'operator');
   const card=await unicode.hover(token,true);assert(card.querySelector('.lr-reference-notes'));assert.equal(card.querySelector('.lr-reference-syntax').textContent,syntax);assert(card.textContent.includes(needle),card.textContent);
  }
  unicode.done();
  const composition=mount(fixture('glossary-composition'),locale),circle=composition.root.querySelectorAll('[data-syntax]').find(node=>node.textContent==='∘'),composite=await composition.hover(circle);assert.equal(circle.dataset.syntax,'operator');assert(composite.querySelector('.lr-reference-notes'));assert.equal(composite.querySelector('.lr-reference-syntax').textContent,'g ∘ f');assert(composite.textContent.includes('g(f(x))'));composition.done();
  for(const [name,spelling,zh,en] of [['glossary-continuity','is_continuous_at','须有定义','must be defined'],['glossary-lipschitz','is_lipschitz','非负实数','nonnegative real'],['glossary-sequence','has_seq_limit','指标为正整数','indexed by positive integers'],['glossary-symmetric-difference','set_diff','只属于其中一个','exactly one']]){
   const view=mount(fixture(name),locale),token=view.root.querySelectorAll('[data-syntax]').find(node=>node.textContent===spelling),card=await view.hover(token);assert(card.textContent.includes(locale==='zh'?zh:en),card.textContent);if(spelling==='set_diff'){assert.equal(token.dataset.syntax,'operator');assert(card.textContent.includes(locale==='zh'?'集合运算符':'Set operator'));}view.done();
  }
  const spaced=mount(fixture('glossary-release-spaced'),locale),phrase=spaced.root.querySelector('[data-keyword="release tuple def"]'),spacedCard=await spaced.hover(phrase);assert(phrase.textContent.includes('\t'));assert(spacedCard.textContent.includes(locale==='zh'?'坐标及维数':'coordinates and dimension'),'canonical help survives authored horizontal whitespace');spaced.done();
 }
 const commented=mount(fixture('glossary-release-comment'),'en');assert.equal(commented.root.querySelectorAll('[data-keyword="release tuple def"]').length,0,'a phrase cannot cross comments or newlines');commented.done();
 const removed=fixture('glossary-removed-predicate');assert.equal(removed.run_result,'failure');assert(JSON.stringify(removed.diagnostics).includes('removed'),'the removed spelling is not presented as a verified predicate');
 const bundle=fixture('glossary-function-cases');bundle.statements.find(s=>s.statement_kind?.endsWith('HaveFnEqualCaseByCaseStmt')).statement_kind='Definition.FutureFunctionStmt';const unknown=mount(bundle,'en'),token=unknown.root.querySelector('[data-keyword="have fn"]'),generic=await unknown.hover(token);assert(!generic.textContent.includes('mutually compatible cases'),'an unknown statement kind gets no guessed case semantics');unknown.done();
 console.log(JSON.stringify({passed:true,bilingualSpecificStatementHelp:true,threeWordPhrases:true,domainAndArityAccurate:true,checkedWalkthroughPreserved:true,keyboardFocus:true,resolvedSetIdentity:true,numerals:true,unknownKindsNotGuessed:true,proofRecordsUnchanged:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
