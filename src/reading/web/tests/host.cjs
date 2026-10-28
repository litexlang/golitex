"use strict";
// Unmodified app + reader, actual exported parts, and an actual release verifier.
// The transport is file-backed/in-memory; no browser or network is accessed.
const fs=require("node:fs"),path=require("node:path"),vm=require("node:vm"),assert=require("node:assert/strict"),{execFile}=require("node:child_process");
const {createDOM}=require("./dom.cjs");
const [input,binary,output]=process.argv.slice(2);
if(!input||!binary||!output)throw new Error("Usage: node host.cjs <three-chapter-book-export> <release-litex> <task-owned-output>");
const directory=path.resolve(input),scratch=path.resolve(output),executable=path.resolve(binary);
assert(scratch!==directory&&!scratch.startsWith(directory+path.sep),"keep generated requests outside the exported site");
fs.mkdirSync(scratch,{recursive:true});
const readerCode=fs.readFileSync(path.join(__dirname,"../reader.js"),"utf8"),appCode=fs.readFileSync(path.join(__dirname,"../app.js"),"utf8");
const initial=JSON.parse(fs.readFileSync(path.join(directory,"reading.manifest.json"),"utf8"));
assert.equal(initial.sources.length,3,"use examples/reading/book");
const sleep=ms=>new Promise(resolve=>setTimeout(resolve,ms));
async function until(test,message){const end=Date.now()+20000;while(!test()){if(Date.now()>end)throw new Error(message);await sleep(10);}}
async function open({referrer="",parent=null,holdResult}={}){
  const dom=createDOM(),{document,window}=dom,requests=[],reads=[],messages=[];
  const node=(tag,id,text="")=>{const value=document.createElement(tag);value.id=id;value.textContent=text;document.body.append(value);return value;};
  node("script","reading-data",JSON.stringify(initial));node("select","language");node("label","language-label");node("div","upload-status");
  node("input","source-files");node("input","project-files");const root=node("main","reader");node("script","reading-build-endpoint","/api/reading/build");
  document.referrer=referrer;
  window.parent=parent||window;
  if(parent)parent.postMessage=(data,origin)=>messages.push({data,origin});
  const location={href:"https://reading.test/index.html?lang=en",search:"?lang=en",origin:"https://reading.test",protocol:"https:"};
  const fetch=async(url,options={})=>{
    if(options.method==="POST"){
      assert.equal(url,"/api/reading/build");const body=JSON.parse(options.body);assert.equal(body.strict,true);assert.equal(body.entry.kind,"file");
      const work=path.join(scratch,"request-"+String(open.serial++).padStart(3,"0"));fs.mkdirSync(work,{recursive:true});
      fs.writeFileSync(path.join(work,"payload.json"),JSON.stringify(body,null,2));
      for(const file of body.files){
        assert(typeof file.path==="string"&&!path.isAbsolute(file.path)&&!file.path.split(/[\\/]/).includes(".."));
        const target=path.resolve(work,file.path);assert(target.startsWith(work+path.sep));fs.mkdirSync(path.dirname(target),{recursive:true});fs.writeFileSync(target,file.content);
      }
      const args=["-reading","-json","-strict","-lang",body.language,"-f",path.join(work,body.entry.path)];
      const outcome=await new Promise((resolve,reject)=>execFile(executable,args,{maxBuffer:32*1024*1024,timeout:60000},(error,stdout,stderr)=>{
        if(error&&error.code!==1){reject(new Error(stderr||error.message));return;}resolve({exit:error?1:0,stdout,stderr});
      }));
      const data=JSON.parse(outcome.stdout);assert.equal(data.kind,"reading");assert.equal(outcome.exit,data.run_result==="success"?0:1);
      fs.writeFileSync(path.join(work,"reading.json"),outcome.stdout);
      requests.push({body,exit:outcome.exit,result:JSON.parse(outcome.stdout),directory:work});
      if(holdResult)await holdResult(data);
      return {ok:true,json:async()=>data};
    }
    const target=new URL(url,location.href);assert.equal(target.origin,location.origin);
    const file=path.resolve(directory,decodeURIComponent(target.pathname.slice(1)));assert(file.startsWith(directory+path.sep));
    const text=fs.readFileSync(file,"utf8");reads.push(target.pathname.slice(1));return {ok:true,json:async()=>JSON.parse(text)};
  };
  const context=vm.createContext({...dom,location,fetch,TextEncoder,URL,URLSearchParams,Map,Set,setTimeout,clearTimeout,console});vm.runInContext(readerCode,context);
  let reader;const original=window.LitexReading;
  window.LitexReading={...original,mount(...args){reader=original.mount(...args);return reader;},async open(...args){reader=await original.open(...args);return reader;}};
  await vm.runInContext(appCode,context);
  return {...dom,root,reader,requests,reads,messages,async chapter(index){const links=root.querySelectorAll("button.lr-chapter");assert.equal(links.length,3);await links[index].click();},row(line){return root.querySelector('[data-line="'+line+'"]');}};
}
open.serial=1;
async function run(){
  const page=await open();await page.chapter(1);
  let editor=page.root.querySelector(".lr-ide-input");const original=editor.value;
  assert(original.includes("above_zero(1)"));assert(page.row(1).querySelector(".lr-inference-toggle"));
  editor.value=original.replace("above_zero(1)","above_zero(-1)");await editor.trigger("input");
  assert(page.root.querySelector(".lr-pending"));assert.equal(page.root.querySelectorAll(".lr-inline-inferences,.lr-chain-equality,.lr-token").length,0);
  await page.root.querySelector(".lr-check").click();
  assert.equal(page.requests.length,1);const failed=page.requests[0];assert.equal(failed.result.run_result,"failure");
  assert.equal(failed.result.sources.length,2,"the actual native target stops before chapter 3");
  assert.equal(failed.body.files.filter(file=>file.path.endsWith(".lit")).length,3);
  assert(page.reads.includes(initial.sources[2].source_url),"the shell prepares later source through its lightweight part");
  assert(!page.reads.includes(initial.sources[2].chunk_url),"checking must not load later proof");
  let marker=page.row(1).querySelector(".lr-inline-failure");assert(marker);await marker.trigger("mouseenter");await sleep(480);
  assert(page.root.querySelector(".lr-proof-popover").textContent.includes("(-1) > 0"));
  const later=failed.result.statements.find(statement=>statement.source_id===failed.result.sources[1].id&&statement.line===2);assert(later&&later.status==='accepted','the native verifier independently checks the next statement in this file');
  assert(JSON.parse(page.row(2).dataset.proofFacts).includes(later.mathematics.subject_fact_id),'an independently accepted statement exposes its fresh proof from this failed overall run');
  await page.chapter(0);const priorChapterStatus=page.root.querySelector(".lr-book-heading").textContent;
  assert(priorChapterStatus.includes("Last check failed"),"a global check failure must not claim that this accepted chapter failed");
  await page.chapter(2);assert(page.root.querySelector(".lr-pending").textContent.includes("Chapter not checked"));
  assert(page.root.querySelector(".lr-pending").textContent.includes("earlier steps failed"));
  assert.equal(page.root.querySelectorAll(".lr-inline-inferences,.lr-chain-equality,.lr-token").length,0);
  await page.root.querySelector(".lr-check").click();assert.equal(page.requests[1].result.run_result,"failure");
  assert(!page.root.querySelector(".lr-editor-error"),page.root.querySelector(".lr-editor-error")?.textContent);
  assert(page.root.querySelector(".lr-inline-failure"),"a failed predecessor is shown again when checking a later chapter; actual: "+page.reader.getSelection().source+" / "+page.root.querySelector(".lr-book-heading").textContent);
  assert(!page.root.querySelectorAll(".lr-diagnostics").some(node=>node.textContent.includes("failed to import project")));
  assert(page.root.querySelector(".lr-service-diagnostics").textContent.includes("failed to import project"),"the complete service diagnostic remains available in reading help");
  await page.root.querySelector(".lr-restore").click();assert.equal(page.root.querySelector(".lr-ide-input").value,original);
  await page.root.querySelector(".lr-check").click();assert.equal(page.requests[2].result.run_result,"success");
  assert.equal(page.requests[2].result.sources.length,2);assert(page.row(1).querySelector(".lr-inference-toggle"));
  await page.chapter(2);assert(page.root.querySelector(".lr-pending").textContent.includes("Chapter not checked"));
  assert(page.root.querySelector(".lr-pending").title.includes("Check this chapter to continue"));
  const before=page.requests.length;editor=page.root.querySelector(".lr-ide-input");await editor.trigger("keydown",{key:"Enter",ctrlKey:true});
  await until(()=>page.requests.length>before&&!page.root.querySelector(".lr-check").disabled,"keyboard checking did not settle");
  assert.equal(page.requests.at(-1).result.run_result,"success");assert.equal(page.requests.at(-1).result.sources.length,3);
  assert(!page.root.querySelector(".lr-pending"));assert(page.row(5).querySelector(".lr-chain-equality"));
  await page.row(5).querySelector(".lr-line-number").click();assert(!page.root.querySelector(".lr-context-explanation").hidden,"line-number tap exposes a source-local explanation without modifier keys");
  await page.root.trigger("keydown",{key:"Escape"});assert(page.root.querySelector(".lr-context-explanation").hidden);
  page.reader.destroy();

  let release,arrived;const held=new Promise(resolve=>{release=resolve;}),started=new Promise(resolve=>{arrived=resolve;});
  const navigating=await open({holdResult:async()=>{arrived();await held;}});await navigating.chapter(1);
  const draft=navigating.root.querySelector(".lr-ide-input");draft.value=draft.value.replace("above_zero(1)","above_zero(-1)");await draft.trigger("input");
  const checking=navigating.root.querySelector(".lr-check").click();await started;await navigating.chapter(2);
  assert.equal(navigating.root.querySelector(".lr-ide-input").dataset.sourcePath,"03-local-proofs.lit","the reader moved before the response was released");
  release();await checking;
  assert.equal(navigating.root.querySelector(".lr-ide-input").dataset.sourcePath,"03-local-proofs.lit","a failed response must preserve the chapter the reader moved to");
  assert(navigating.root.querySelector(".lr-pending").textContent.includes("earlier steps failed"));navigating.reader.destroy();

  const parent={},embedded=await open({referrer:"https://textbook.test/lesson/",parent});
  const ready=embedded.messages.find(message=>message.data.type==="litex-reading:ready");assert(ready);assert.equal(ready.origin,"https://textbook.test");
  assert.equal(ready.data.bundle_id,embedded.reader.getBundleId());
  const full=JSON.parse(fs.readFileSync(path.join(directory,"reading.json"),"utf8")),fact=full.facts.find(fact=>fact.source_id===initial.sources[2].id&&fact.role==="verified"&&fact.line===5);
  assert(fact);const other=full.facts.find(item=>item.id!==fact.id),select={type:"litex-reading:select",bundle_id:ready.data.bundle_id,fact_id:fact.id};
  await embedded.window.dispatch("message",{origin:"https://textbook.test",source:parent,data:select});
  await until(()=>embedded.reader.getSelection().fact===fact.id,"embedded fact selection did not settle");
  assert(embedded.reads.includes(initial.sources[2].chunk_url));
  assert.equal(embedded.messages.at(-1).data.selection.fact,fact.id);assert.equal(embedded.messages.at(-1).origin,"https://textbook.test");
  const current=embedded.reader.getSelection();
  for(const event of [
    {origin:"https://outside.example",source:parent,data:{...select,fact_id:other.id}},
    {origin:"https://textbook.test",source:{},data:{...select,fact_id:other.id}},
    {origin:"https://textbook.test",source:parent,data:{...select,bundle_id:"old-bundle",fact_id:other.id}}
  ]){await embedded.window.dispatch("message",event);assert.deepEqual(embedded.reader.getSelection(),current);}
  const noticeCount=embedded.messages.length,readCount=embedded.reads.length,unloaded=full.facts.find(item=>item.source_id===initial.sources[1].id);
  assert(unloaded);const staleCheck=embedded.root.querySelector(".lr-check");embedded.reader.destroy();await embedded.window.dispatch("scroll");await embedded.window.dispatch("resize");
  await embedded.window.dispatch("message",{origin:"https://textbook.test",source:parent,data:{...select,fact_id:unloaded.id}});
  await sleep(10);assert.equal(embedded.reads.length,readCount,"a disposed reader must not fetch proof for a late parent message");
  await staleCheck.click();assert.equal(embedded.requests.length,0,"a disposed reader must not start a new verifier request");
  await assert.rejects(embedded.reader.getProjectSnapshot(),/closed/);
  embedded.reader.update(full);assert.equal(embedded.messages.length,noticeCount,"a disposed reader does not announce updates");
  assert.equal(embedded.messages.length,noticeCount);
  for(const referrer of ["file:///tmp/book.html","data:text/html,chapter","not a URL"]){
    const view=await open({referrer,parent:{}});assert.equal(view.messages.length,0,"an opaque or invalid referrer must not enable parent messaging");assert(view.root.querySelector(".lr-ide-input"));view.reader.destroy();
  }
  const changedParent={},changed=await open({referrer:"https://textbook.test/lesson/",parent:changedParent}),oldBundle=changed.reader.getBundleId();
  changed.reader.update(page.requests[0].result);assert.notEqual(changed.reader.getBundleId(),oldBundle);
  const unchanged=changed.reader.getSelection(),currentFact=page.requests[0].result.facts.find(fact=>fact.role==="verified");assert(currentFact);
  await changed.window.dispatch("message",{origin:"https://textbook.test",source:changedParent,data:{type:"litex-reading:select",bundle_id:oldBundle,fact_id:currentFact.id}});
  assert.deepEqual(changed.reader.getSelection(),unchanged,"a reused FactId from an older real bundle does not change the new document");
  await changed.window.dispatch("message",{origin:"https://textbook.test",source:changedParent,data:{type:"litex-reading:select",bundle_id:changed.reader.getBundleId(),fact_id:currentFact.id}});
  await until(()=>changed.reader.getSelection().fact===currentFact.id,"current-bundle selection failed");
  const oldToken=changed.root.querySelector(".lr-token"),working=changed.root.querySelector(".lr-ide-input");assert(oldToken);
  working.value+="\n# local draft";working.setSelectionRange(working.value.length,working.value.length);await working.trigger("input");
  const cleared=changed.reader.getSelection();assert.equal(cleared.fact,null);assert.equal(cleared.statement,null);assert.equal(changed.messages.at(-1).data.selection.fact,null);
  assert.equal(await changed.reader.selectFact(currentFact.id),false);assert.equal(await changed.reader.selectStatement(page.requests[0].result.statements[0].id),false);
  const wd=page.requests[0].result.well_definedness[0];assert(wd);assert.equal(await changed.reader.selectWellDefinedness(wd.id),false);
  await oldToken.click();assert.deepEqual(changed.reader.getSelection(),cleared,"stale source controls cannot restore old semantic selections");changed.reader.destroy();
  const report={passed:true,actualChecks:[...page.requests,...navigating.requests].map(request=>({target:request.body.entry.path,exit:request.exit,result:request.result.run_result,sources:request.result.sources.length})),
    freshFailureAndInference:true,laterSourceWithoutOldProof:true,restoreAndKeyboardCheck:true,lineNumberTapAndEscape:true,priorChapterStatus,
    iframeReadyAndSelection:true,iframeOriginSourceAndBundleGuards:true,opaqueReferrerKeepsReadingWithoutMessaging:true,
    disposedReaderRejectsWork:true,navigationPreservedDuringFailedCheck:true,realBundleChangeRejectsOldSelection:true,
    editedDraftClearsParentSelectionAndRejectsOldIds:true};
  fs.writeFileSync(path.join(scratch,"acceptance.json"),JSON.stringify(report,null,2)+"\n");console.log(JSON.stringify(report,null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
