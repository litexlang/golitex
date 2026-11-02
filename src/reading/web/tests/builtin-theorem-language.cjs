'use strict';
// Semantic theorem descriptions follow retained native identities, not names.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {createDOM}=require('./dom.cjs'),directory=process.argv[2];
if(!directory)throw new Error('Usage: node builtin-theorem-language.cjs <builtin-reference-fixtures>');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),cards=JSON.parse(fs.readFileSync(path.join(__dirname,'../../language_reference.json'),'utf8')).builtin_theorems;
const fixture=name=>JSON.parse(fs.readFileSync(path.join(directory,'builtin-reference-'+name+'.json'),'utf8'));
function records(bundle){const nodes=new Map(bundle.evidence_nodes.map(row=>[row.id,row.node]));const resolve=value=>{while(value?.kind==='evidence_reference')value=nodes.get(value.evidence_id);return value||{};};return {nodes,resolve};}
function removeDeclarations(bundle){for(const symbol of bundle.symbols){delete symbol.builtin_theorem;if(symbol.kind==='builtin_theorem')delete symbol.kind;}}
function mount(bundle,locale){
 const dom=createDOM(),root=dom.root(),before=JSON.stringify(bundle),timers=new Map();let serial=0,checks=0;
 vm.runInContext(code,vm.createContext({...dom,console,TextEncoder,URL,Map,Set,setTimeout(fn){timers.set(++serial,fn);return serial;},clearTimeout(id){timers.delete(id);}}));
 const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck:async()=>{checks++;return bundle;}});
 return {...dom,root,reader,checks:()=>checks,token(name){return root.querySelectorAll('[data-symbol]').find(n=>n.closest('.lr-source-code')&&n.textContent===name);},async hover(target,focus=false){assert(target);const selection=JSON.stringify(reader.getSelection());if(focus)await target.trigger('focus');else{dom.document.elementFromPoint=()=>target;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}for(let round=0;round<3;round++)for(const [id,fn]of [...timers])if(timers.has(id)){timers.delete(id);fn();}assert.equal(JSON.stringify(reader.getSelection()),selection);const symbol=root.querySelector('.lr-proof-symbol'),tip=symbol&&!symbol.hidden?symbol:root.querySelector('.lr-token-help')||root.querySelector('.lr-proof-popover');assert(tip,target.textContent);return tip;},done(){assert.equal(JSON.stringify(bundle),before,'semantic descriptions do not rewrite source or proof data');reader.destroy();}};
}
function failureReports(card){return card.querySelectorAll('.lr-theorem-failure,.lr-failure-summary').filter(node=>!node.parentNode?.closest('.lr-theorem-failure'));}
async function run(){
 let checks=0;
 for(const locale of ['zh','en'])for(const [identity,card]of Object.entries(cards)){
  const bundle=fixture(identity);assert.equal(bundle.run_result,'success',identity);assert(bundle.sources.some(s=>s.content===card.example),'the checked source is exactly the displayed example');const data=records(bundle);assert([...data.nodes.values()].some(n=>n.type==='BuiltinTheoremId'&&n.variant===identity),identity);
  const view=mount(bundle,locale),token=view.token(card.syntax.split('(')[0]);assert(token);assert.equal(token.dataset.syntax,'theorem');
  for(const focus of [false,true]){const tip=await view.hover(token,focus);assert.equal(tip.querySelector('.lr-reference-kind').textContent,card.kind[locale]);assert.equal(tip.querySelector('.lr-reference-syntax').textContent,card.syntax);assert(tip.textContent.includes(card.summary[locale]));assert(tip.textContent.includes(card.notes[locale]));assert.equal(tip.querySelector('.lr-reference-example').textContent,card.example);checks++;}
  await token.click();assert.equal(view.reader.getSelection().symbol,token.dataset.symbol);assert(view.root.querySelector('.lr-detail-body').textContent.includes(card.notes[locale]));assert.equal(view.checks(),0);view.done();
 }
 const id='FiniteSetHasBijectiveIndex',card=cards[id],name=card.syntax.split('(')[0];
 for(const control of ['missing-identity','future','prototype','wrong-type','wrong-rule','malformed-variant','missing-callee']){
  const bundle=fixture(id);removeDeclarations(bundle);const data=records(bundle),application=[...data.nodes.values()].find(n=>n.type==='BuiltinThmApplication'),theorem=data.resolve(application.fields.theorem);
  if(control==='missing-identity')delete application.fields.theorem;
  if(control==='future'){theorem.variant='FutureTheorem';delete theorem.rule_id;}
  if(control==='prototype'){theorem.variant='__proto__';delete theorem.rule_id;}
  if(control==='wrong-type')theorem.type='DefThmStmt';
  if(control==='wrong-rule')theorem.rule_id='builtin_theorem.BuiltinTheoremId::PrimeDivisor';
  if(control==='malformed-variant')theorem.variant={toString:'not a function'};
  if(control==='missing-callee')for(const n of data.nodes.values())if(n.type==='ExecReleaseThmStmtSuccess')delete n.fields.callee;
  const view=mount(bundle,'en'),tip=await view.hover(view.token(name));assert(!tip.textContent.includes(card.summary.en),control+': a spelling alone cannot supply the explanation');view.done();
 }
 const legacy=fixture(id);removeDeclarations(legacy);legacy.rules=[];for(const row of legacy.evidence_nodes)if(row.node.type==='BuiltinTheoremId')delete row.node.rule_id;const older=mount(legacy,'en');assert((await older.hover(older.token(name))).textContent.includes(card.notes.en),'the retained typed identity is sufficient without catalogue text');older.reader.setLanguage('zh');assert((await older.hover(older.token(name))).textContent.includes(card.notes.zh));assert.equal(older.checks(),0);older.done();
 const user=mount(fixture('FiniteSetSumSubstitution'),'en'),userToken=user.token('substitution'),userTip=await user.hover(userToken);assert(userTip.querySelector('.lr-definition-source'),'a user theorem keeps its own source declaration');assert(!userTip.querySelector('.lr-reference-kind'));user.done();
 let rejectedChecks=0;
 const rejections=[['prime-domain','PrimeDivisor'],['selected-prime-domain','PrimeDivisor'],['finite-arity','FiniteSetHasBijectiveIndex'],['fold-shape','FiniteSetReduceSingleton'],['sum-order','FiniteSetSumLessEqualFromPointwise'],['choice-family','IndexCartesianNonemptyByChoiceFromFamily'],['tuple-domain','TupleEqualFromCoordinates'],['cart-domain','CartesianMemberFromCoordinates'],['function-domain','FunctionSetMember'],['builder-condition','SetBuilderMember'],['defined-condition','DefinedSetMember'],['structure-fields','StructMember'],['family-empty','FamilyIntersectionMember'],['family-missing-membership','FamilyIntersectionMemberFacts'],['index-fiber','IndexedIntersectionMember'],['upper-candidate','RealLeastUpperBoundFromDefinition'],['lower-candidate','RealGreatestLowerBoundFromDefinition'],['upper-empty','RealLeastUpperBoundExists'],['lower-empty','RealGreatestLowerBoundExists'],['density-equal','RationalBetweenReals']];
 rejections.push(['seq-no-candidate','SequenceLimitAdd'],['seq-no-epsilon-proof','SequenceLimitFromEpsilon'],['seq-tail-zero','SequenceLimitTail'],['seq-complex-scale','SequenceLimitScale'],['seq-power-negative','SequenceLimitPower'],['seq-shift-negative','SequenceLimitShift'],['seq-eventual-false','SequenceLimitEventuallyEqual'],['seq-compare-false','SequenceLimitCompare'],['seq-squeeze-false','SequenceLimitSqueeze'],['seq-missing-denom-terms','SequenceLimitDivide'],['seq-missing-denom-limit','SequenceLimitDivide'],['seq-selected-no-existence','SequenceLimitSelected'],['seq-finite-domain','SequenceLimitConstant']);
 for(const [side,prefix]of [['limsup','SequenceLimsup'],['liminf','SequenceLiminf']])for(const [name,suffix]of [['wrong-negation','ScaleNonnegative'],['negation-kind','Neg'],['zero-negative-scale','ScaleNegative'],['zero-hit-epsilon','Hit'],['zero-hit-cutoff','Hit'],['selected-no-existence','Selected'],['sum-no-bounds','SumBound'],['add-no-convergence','AddConvergent'],['bounded-zero','BoundedExists'],['missing-tail-hits','FromEpsilon']])rejections.push(['extrema-'+side+'-'+name,prefix+suffix]);
 const receipt=JSON.parse(fs.readFileSync(path.join(directory,'verification.json'),'utf8')),nativeRejections=Object.entries(receipt).filter(([key,value])=>key.startsWith('builtin-reference-')&&value.run_result==='failure').map(([key])=>key.slice('builtin-reference-'.length));
 assert.deepEqual(nativeRejections.sort(),rejections.map(([name])=>name).sort(),'every native rejected theorem fixture must exercise its source help');
 for(const locale of ['zh','en'])for(const [fixtureName,identity] of rejections){
  const bundle=fixture(fixtureName),card=cards[identity],name=card.syntax.split('(')[0];assert.equal(bundle.run_result,'failure');const view=mount(bundle,locale),row=view.root.querySelector('.lr-rejected'),token=view.token(name);assert(row,fixtureName);assert(token,fixtureName+': the rejected call must retain its theorem token');assert.equal(token.dataset.syntax,'theorem');
  for(const focus of [false,true]){const tip=await view.hover(token,focus);assert(tip.textContent.includes(card.notes[locale]),fixtureName);assert.equal(tip.querySelector('.lr-reference-kind').textContent,card.kind[locale]);assert(!view.root.querySelector('.lr-proof-popover .lr-theorem-application'),'a rejected call has no successful theorem application');rejectedChecks++;}
  await token.click();assert(view.root.querySelector('.lr-detail-body').textContent.includes(card.notes[locale]));assert.equal(view.checks(),0);view.done();
 }
 for(const control of ['missing','wrong-type','wrong-name','wrong-arity','missing-kind','prototype','null']){
  const bundle=fixture('prime-domain'),symbol=bundle.symbols.find(s=>s.name==='prime_divisor');assert(symbol.builtin_theorem,'native rejection must retain declaration identity');
  if(control==='missing')removeDeclarations(bundle);
  if(control==='wrong-type')symbol.builtin_theorem.type='TheoremCall';
  if(control==='wrong-name')symbol.builtin_theorem.name='finite_set_has_bijective_index';
  if(control==='wrong-arity')symbol.builtin_theorem.arity=2;
  if(control==='missing-kind')delete symbol.kind;
  if(control==='prototype')symbol.builtin_theorem.name='__proto__';
  if(control==='null')symbol.builtin_theorem=null;
  const view=mount(bundle,'en'),tip=await view.hover(view.token('prime_divisor'));assert(!tip.textContent.includes(cards.PrimeDivisor.summary.en),control);assert(!view.root.querySelector('.lr-proof-popover .lr-theorem-application'));view.done();
 }
 for(const invalid of ['arity','null']){const conflict=fixture(id),symbol=conflict.symbols.find(s=>s.name===name);if(invalid==='arity')symbol.builtin_theorem.arity=2;else symbol.builtin_theorem=null;const cv=mount(conflict,'en');assert(!(await cv.hover(cv.token(name))).textContent.includes(card.notes.en),'conflicting source and execution identities fail closed');cv.done();}
 const sourceOnly=fixture(id);for(const row of sourceOnly.evidence_nodes)if(row.node.type==='ExecReleaseThmStmtSuccess'){delete row.node.fields.callee;delete row.node.fields.builtin;}const sv=mount(sourceOnly,'en');assert((await sv.hover(sv.token(name))).textContent.includes(card.notes.en),'declaration help does not require application success evidence');sv.done();
 for(const locale of ['zh','en']){
  const nested=fixture('seq-no-candidate'),statement=nested.statements.find(s=>s.status==='rejected'&&s.statement_kind?.endsWith('ReleaseThmStmt'));assert(statement);
  const view=mount(nested,locale),row=view.root.querySelector('[data-line="'+statement.line+'"]');assert(row.classList.contains('lr-rejected'),'the actual failed child owns its source error state');
  const card=await view.hover(row.querySelector('.lr-source-code'));assert(card.textContent.includes('has_seq_limit'),card.textContent);assert(!card.querySelector('.lr-theorem-application'));
  assert.equal(failureReports(card).length,1,'one retained failed child produces one report, not a repeated enclosing failure');
  await card.querySelector('.lr-proof-pin').click();assert.equal(view.reader.getSelection().statement,statement.id,'pinning follows the actual failed child');view.done();
 }
 for(const control of ['legacy','wrong-parent','different-line']){
  const nested=fixture('seq-no-candidate'),statement=nested.statements.find(s=>s.status==='rejected'&&s.statement_kind?.endsWith('ReleaseThmStmt')),parent=nested.statements.find(s=>s.id===statement.parent_statement_id),data=records(nested);
  if(control==='legacy')for(const node of data.nodes.values())if(node.type==='ProofBlockBodyFailed')node.fields.result=statement.evidence;
  if(control==='wrong-parent')statement.parent_statement_id=null;
  if(control==='different-line')parent.failure.source_location.line=1;
  const view=mount(nested,'en'),row=view.root.querySelector('[data-line="'+statement.line+'"]'),card=await view.hover(row.querySelector('.lr-source-code'));
  assert(card.textContent.includes('has_seq_limit'));assert.equal(failureReports(card).length,control==='different-line'?1:2,'reports are suppressed only by an exact same-row retained child relationship');view.done();
 }
 console.log(JSON.stringify({passed:true,theoremDescriptions:Object.keys(cards).length,bilingualHoverFocus:checks,rejectedBilingualHoverFocus:rejectedChecks,nestedFailedCallSourceHover:true,clickAndLocale:true,realExampleSources:true,typedIdentityRequired:true,declarationIndependentOfSuccess:true,legacyCompatible:true,userTheoremUnchanged:true,noReverification:true,rejectionsNotSuccess:true,sourceAndEvidenceUnchanged:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
