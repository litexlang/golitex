"use strict";
// Public mount API + actual DOM event handlers; no source rewriting/test hooks.
const fs=require("node:fs"),path=require("node:path"),vm=require("node:vm"),assert=require("node:assert/strict");
const {createDOM}=require("./dom.cjs");
const directory=process.argv[2];
if(!directory)throw new Error("Usage: node src/reading/web/tests/run.cjs <fixture-directory>");
const code=fs.readFileSync(path.join(__dirname,"../reader.js"),"utf8");
const delay=()=>new Promise(resolve=>setTimeout(resolve,480));
function deferred(){let resolve,reject;const promise=new Promise((yes,no)=>{resolve=yes;reject=no;});return {promise,resolve,reject};}
function fixture(name){return JSON.parse(fs.readFileSync(path.join(directory,name+".json"),"utf8"));}
function mount(bundle,options={}){
  const dom=createDOM(),root=dom.root();
  vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,setTimeout,clearTimeout,console}));
  const reader=dom.window.LitexReading.mount(root,{document:bundle,locale:"zh",...options});
  return {...dom,root,reader,row(line){return root.querySelector('[data-line="'+line+'"]');}};
}
async function proofAt(view,line){
  const row=view.row(line),target=row.querySelector('.lr-syntax-predicate')||row;
  await row.trigger("pointermove",{target});await delay();
  const card=view.root.querySelector(".lr-proof-popover");assert(card,"proof card for line "+line);return card;
}
async function run(){
  const evidence={};
  const logic=mount(fixture("syllogism"));
  assert.equal(logic.root.querySelectorAll(".lr-json-pane,.lr-json-toggle").length,0);
  assert(logic.root.querySelector(".lr-context-explanation").hidden);
  let card=await proofAt(logic,14);
  assert(card.textContent.includes("person = socrates"),"current Detailed result retains the substitution");
  const premises=card.querySelectorAll(".lr-proof-grounds .lr-fact-link").map(node=>node.textContent);
  assert(premises.some(text=>text.includes("is_human(socrates)")));
  assert(premises.some(text=>text.includes("is_mortal(person)")));
  evidence.syllogism={premises,concreteSubstitution:true};
  logic.reader.setLanguage("en");card=await proofAt(logic,14);
  assert(card.textContent.includes("Take person = socrates"));logic.reader.destroy();

  const source=fixture("sqrt-two"),original=JSON.stringify(source),view=mount(source,{onCheck:async()=>source});
  const input=view.root.querySelector(".lr-ide-input"),row=view.row(7);
  input.setSelectionRange(input.value.split("\n").slice(0,6).reduce((count,line)=>count+line.length+1,0),0);
  view.document.elementFromPoint=()=>row.querySelector(".lr-source-code");
  await input.trigger("click",{clientX:100,clientY:80});
  assert.equal(view.reader.getSelection().statement,"statement3");
  assert(view.root.querySelector(".lr-context-explanation").hidden,"ordinary editing must not summon an inspector");
  const equals=view.row(7).querySelectorAll(".lr-chain-equality");assert.equal(equals.length,3);
  const relations=[],stepPremises=[];
  for(const token of equals){
    view.document.elementFromPoint=()=>token;await input.trigger("pointermove",{clientX:100,clientY:80});await delay();
    const preview=view.root.querySelector(".lr-proof-popover");assert(preview);
    relations.push(preview.querySelector(".lr-proof-part .lr-formula").textContent);
    stepPremises.push(preview.querySelectorAll(".lr-proof-grounds .lr-fact-link").map(node=>node.textContent));
    assert(!preview.textContent.includes("分别验证每个相邻关系"));
  }
  assert.equal(new Set(relations).size,3);assert(stepPremises[0].some(text=>text.includes("sqrt (2) = (p / q)")),JSON.stringify(stepPremises));
  assert(!stepPremises[1].some(text=>text.includes("sqrt (2) = (p / q)")));
  view.document.elementFromPoint=()=>equals[0];await input.trigger("pointermove",{clientX:100,clientY:80});await delay();
  const cite=view.root.querySelector(".lr-proof-grounds .lr-fact-link");assert(cite);
  await cite.trigger("mouseenter");assert(view.row(5).classList.contains("lr-citation-peek"));
  await cite.click();assert.equal(view.reader.getSelection().fact,cite.dataset.fact);
  await view.root.querySelector(".lr-back").click();
  assert.equal(view.reader.getSelection().chainStep,0,"return to the exact hovered equality, not the enclosing proof's start");
  assert.equal(view.root.querySelector(".lr-detail-body .lr-formula").textContent,relations[0]);
  const last=view.row(7).querySelectorAll(".lr-chain-equality")[2],current=view.root.querySelector(".lr-ide-input");
  view.document.elementFromPoint=()=>last;await current.trigger("pointermove",{clientX:100,clientY:80});await delay();
  await view.root.querySelector(".lr-proof-pin").click();
  assert.equal(view.reader.getSelection().chainStep,2);
  assert.equal(view.root.querySelector(".lr-detail-body .lr-formula").textContent,relations[2]);
  await view.root.trigger("keydown",{key:"Escape"});assert.equal(view.document.activeElement,view.root.querySelector(".lr-ide-input"),"Escape returns editing focus after a pinned proof");
  const rows=view.root.querySelectorAll(".lr-code-row").length;
  const edited=view.root.querySelector(".lr-ide-input");edited.value+=" ";await edited.trigger("input");
  assert.equal(view.root.querySelectorAll(".lr-inline-inferences,.lr-chain-equality,.lr-proof-popover").length,0);
  assert.equal(view.root.querySelectorAll(".lr-code-row").length,rows);
  assert.equal(JSON.stringify(source),original);view.reader.destroy();
  evidence.equalitySteps={relations,stepPremises,ordinaryEditingIsUnobstructed:true,citationPeekAndExactReturn:true};

  const keyboard=mount(fixture("sqrt-two"),{locale:"en"}),firstEquality=keyboard.row(7).querySelector(".lr-chain-equality");
  firstEquality.focus();await delay();
  assert(keyboard.root.querySelector(".lr-proof-popover").textContent.includes("Why this equality holds"));
  await firstEquality.trigger("keydown",{key:"Enter"});
  assert.equal(keyboard.reader.getSelection().chainStep,0);
  assert.equal(keyboard.root.querySelector(".lr-detail-body .lr-formula").textContent,relations[0]);
  keyboard.root.querySelector(".lr-detail-body").focus();await keyboard.root.trigger("keydown",{key:"Escape"});
  assert.equal(keyboard.document.activeElement.dataset.chainStep,"0","read-only Escape returns to the exact equality target");await delay();
  assert(!keyboard.root.querySelector(".lr-proof-popover"),"restoring source focus does not immediately reopen the explanation");
  await keyboard.row(7).querySelector(".lr-line-number").click();
  assert.equal(keyboard.reader.getSelection().chainStep,null,"line selection restores the complete chain");
  keyboard.reader.destroy();

  // Exercise degraded exported records through the public renderer as well.
  // Missing evidence must never borrow the proof of another adjacent step.
  const controls={};
  for(const name of ["missingProof","wrongEndpoint","missingOperator","ambiguousPrimary"]){
    const bundle=fixture("sqrt-two"),nodes=new Map(bundle.evidence_nodes.map(item=>[item.id,item.node]));
    const resolve=value=>{while(value?.kind==="evidence_reference")value=nodes.get(value.evidence_id);return value;};
    const primary=bundle.facts.find(fact=>fact.line===7&&fact.is_primary&&fact.role==="verified");
    let chain=resolve(primary.evidence);while(chain.type!=="VerifyChainFactSuccess")chain=resolve(chain.fields["0"]);
    if(name==="missingProof")chain.fields.adjacent[0]={kind:"unavailable"};
    if(name==="wrongEndpoint"){
      let step=resolve(chain.fields.adjacent[0]);while(step.type!=="VerifyEqualitySuccess")step=resolve(step.fields["0"]);
      resolve(step.fields.fact).fields.left={kind:"evidence_reference",evidence_id:"missing-test-endpoint"};
    }
    if(name==="missingOperator"){
      const tokens=bundle.sources[0].tokens,equals=tokens.filter(token=>token.text==="=");
      // The chain has three adjacent equals tokens; its first token is found
      // by the same exact line byte interval retained in the source snapshot.
      const offset=Buffer.byteLength(bundle.sources[0].content.split("\n").slice(0,6).join("\n")+"\n");
      const token=equals.find(token=>token.start_byte>=offset);assert(token);
      tokens.splice(tokens.indexOf(token),1);
    }
    if(name==="ambiguousPrimary")bundle.facts.push({...primary,id:"test-ambiguous-chain"});
    const degraded=mount(bundle),targets=degraded.row(7).querySelectorAll(".lr-chain-equality").map(token=>Number(token.dataset.chainStep));
    assert.deepEqual(targets,["missingProof","wrongEndpoint"].includes(name)?[1,2]:[],name+" must fail closed");
    controls[name]=targets;degraded.reader.destroy();
  }
  evidence.equalitySteps.keyboardAndLineReset=true;evidence.equalitySteps.degradedRecords=controls;

  const failures={};
  for(const [name,line,obligation] of [["zero-divisor",4,"0 ≠ 0"],["sqrt-domain",4,"0 ≤ (-1)"],["missing-premise",14,"is_mortal(socrates)"]]){
    const failed=mount(fixture(name),{onCheck:async()=>fixture(name)}),marker=failed.row(line).querySelector(".lr-inline-failure");
    assert(marker,name+" has source-local feedback");
    await marker.trigger("mouseenter");await delay();
    const preview=failed.root.querySelector(".lr-proof-popover");assert(preview);
    assert(preview.textContent.includes(obligation),name+" keeps the actual unproved obligation");
    assert(preview.textContent.includes("并不表示这句话为假"));
    if(name==="missing-premise")assert(!failed.row(8).classList.contains("lr-rejected"),"do not mark the entire enclosing forall as the failing line");
    await preview.querySelector(".lr-proof-pin").click();assert(failed.reader.getSelection().issue);
    assert(failed.root.querySelector(".lr-detail-body").textContent.includes(obligation));
    failures[name]={line,obligation};failed.reader.destroy();
  }
  const parse=mount(fixture("undefined-name")),parseNumber=parse.row(3).querySelector(".lr-line-number");
  assert(!parseNumber.disabled,"parse-error lines remain inspectable without a statement record");
  await parseNumber.click();assert(parse.root.querySelector(".lr-detail-body").textContent.includes("undefined name `problem_score`"));
  assert.equal(parse.reader.getSelection().focusLine,3);parse.reader.destroy();
  evidence.sourceFailures=failures;

  const definition=mount(fixture("definition"),{onCheck:async()=>fixture("definition")});
  const editable=definition.root.querySelector(".lr-ide-input"),result=definition.root.querySelector(".lr-inference-toggle");assert(result);
  editable.focus();definition.document.elementFromPoint=()=>result;
  await editable.trigger("pointermove",{clientX:100,clientY:80});await delay();
  let inferred=definition.root.querySelector(".lr-inference-popover");assert(inferred);
  assert.equal(inferred.getAttribute("role"),"region");assert.equal(definition.document.activeElement,editable,"inference hover must not steal typing focus");
  const inferredIds=JSON.parse(result.dataset.facts);assert.equal(inferred.querySelectorAll(".lr-inferred-result").length,inferredIds.length);
  const disclosure=inferred.querySelector('details.lr-inferred-facts'),summary=disclosure.querySelector('summary');assert(disclosure);assert(!disclosure.open,"inferred facts start collapsed");
  assert(disclosure.querySelectorAll('.lr-inferred-result').every(node=>disclosure.contains(node)));
  await result.click();assert.equal(definition.root.querySelector(".lr-inference-popover"),inferred,"click keeps the already hovered results open");
  assert.equal(definition.document.activeElement,summary,"opening the card focuses its collapsed heading");assert(!disclosure.open);
  await summary.click();assert(disclosure.open);await summary.click();assert(!disclosure.open);await summary.click();assert(disclosure.open);
  const selected=inferred.querySelector(".lr-inferred-result");assert.equal(inferred.getAttribute("role"),"dialog");
  await selected.click();assert.equal(definition.reader.getSelection().fact,selected.dataset.fact);
  await definition.root.querySelector(".lr-back").click();assert.equal(definition.reader.getSelection().focusLine,5);
  const badge=definition.root.querySelector(".lr-reference-count");assert(badge);await badge.click();
  const references=definition.root.querySelector(".lr-proof-popover");assert(references.querySelector(".lr-reference-location"));assert.equal(definition.root.querySelectorAll("dialog").length,0);
  await references.querySelector(".lr-explanation-close").click();assert.equal(definition.document.activeElement,badge);await delay();assert(!definition.root.querySelector(".lr-proof-popover"),"closing must not reopen the card on restored focus");
  definition.reader.destroy();evidence.inlineResults={hoverWithoutFocusTheft:true,allIdsRetained:true,followAndReturn:true,sourceAnchoredReferences:true};

  const stale=deferred(),typing=mount(fixture("definition"),{onCheck:()=>stale.promise});
  const pendingCheck=typing.root.querySelector(".lr-check").click();
  let typed=typing.root.querySelector(".lr-ide-input");typed.value+="\n# changed while checking";await typed.trigger("input");
  stale.resolve(fixture("definition"));await pendingCheck;
  assert(typing.root.querySelector(".lr-ide-input").value.endsWith("# changed while checking"));
  assert(typing.root.querySelector(".lr-pending"));assert.equal(typing.root.querySelectorAll(".lr-inline-inferences").length,0);typing.reader.destroy();

  const oldRequest=deferred(),newRequest=deferred();let requests=0;
  const replaced=mount(fixture("definition"),{onCheck:()=>++requests===1?oldRequest.promise:newRequest.promise});
  const oldCheck=replaced.root.querySelector(".lr-check").click();replaced.reader.update(fixture("sets"));
  assert(!replaced.root.querySelector(".lr-check").disabled,"opening a new document cancels the old check's UI lock");
  const newCheck=replaced.root.querySelector(".lr-check").click();oldRequest.resolve(fixture("definition"));await oldCheck;
  assert(replaced.root.querySelector(".lr-check").disabled,"an old finally block must not unlock a newer request");
  newRequest.resolve(fixture("sets"));await newCheck;assert(!replaced.root.querySelector(".lr-check").disabled);assert.equal(replaced.reader.getBundleId(),fixture("sets").bundle_id);replaced.reader.destroy();

  const navigation=deferred(),book=fixture("book"),reading=mount(book,{onCheck:()=>navigation.promise});
  const currentCheck=reading.root.querySelector(".lr-check").click(),next=book.statements.find(statement=>statement.source_id===book.sources[1].id);
  await reading.reader.selectStatement(next.id);navigation.resolve(fixture("book"));await currentCheck;
  assert.equal(reading.reader.getSelection().source,next.source_id,"a completed check must not pull a reader back to an earlier chapter");reading.reader.destroy();

  const offline=mount(fixture("definition"),{onCheck:async()=>{throw new Error("offline checker");}});
  await offline.root.querySelector(".lr-check").click();assert(offline.root.querySelector(".lr-editor-error").textContent.includes("offline checker"));assert(offline.root.querySelector(".lr-context-explanation").hidden);offline.reader.destroy();
  const invalid=mount(fixture("definition"),{onCheck:async()=>({kind:"reading_manifest"})});
  await invalid.root.querySelector(".lr-check").click();assert(invalid.root.querySelector(".lr-editor-error"));assert.equal(invalid.reader.getBundleId(),fixture("definition").bundle_id);invalid.reader.destroy();

  const restored=mount(fixture("definition"),{onCheck:async()=>fixture("definition")}),originalText=restored.root.querySelector(".lr-ide-input").value;
  assert(restored.root.querySelector(".lr-restore").hidden);await restored.root.querySelector(".lr-restore").click();assert(!restored.root.querySelector(".lr-pending"),"restoring identical text is a no-op");
  let draft=restored.root.querySelector(".lr-ide-input");draft.value+="\n# experiment";await draft.trigger("input");
  assert(!restored.root.querySelector(".lr-restore").hidden);
  await restored.root.querySelector(".lr-restore").click();assert.equal(restored.root.querySelector(".lr-ide-input").value,originalText);assert(restored.root.querySelector(".lr-pending"));
  assert(restored.root.querySelector(".lr-restore").hidden);assert.equal(restored.document.activeElement,restored.root.querySelector(".lr-ide-input"));
  await restored.root.querySelector(".lr-check").click();assert(!restored.root.querySelector(".lr-pending"));assert(restored.root.querySelector(".lr-inline-inferences"));restored.reader.destroy();
  evidence.checkingLifecycle={staleResultsIgnored:true,newDocumentCancelsOldLock:true,oldFinallyCannotUnlockNewCheck:true,navigationPreserved:true,hostErrorsVisibleInSource:true,invalidPayloadPreservesDocument:true,restoreRequiresFreshCheck:true};
  console.log(JSON.stringify({passed:true,evidence},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
