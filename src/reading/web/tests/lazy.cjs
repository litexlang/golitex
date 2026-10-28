"use strict";
// Actual exported parts + public API, with a file-backed in-memory fetch adapter.
const fs=require("node:fs"),path=require("node:path"),vm=require("node:vm"),assert=require("node:assert/strict");
const {createDOM}=require("./dom.cjs");
const directory=path.resolve(process.argv[2]||"");
if(!process.argv[2])throw new Error("Usage: node src/reading/web/tests/lazy.cjs <fresh-book-export>");
const code=fs.readFileSync(path.join(__dirname,"../reader.js"),"utf8");
const measure=process.argv.includes("--measure"),original=measure?null:JSON.parse(fs.readFileSync(path.join(directory,"reading.json"),"utf8"));
function deferred(){let resolve;const promise=new Promise(done=>{resolve=done;});return {promise,resolve};}
async function open({legacy=false,changeManifest,respond}={}){
  const manifest=JSON.parse(fs.readFileSync(path.join(directory,"reading.manifest.json"),"utf8"));
  if(legacy)for(const source of manifest.sources)delete source.source_url;
  if(changeManifest)changeManifest(manifest);
  const dom=createDOM(),root=dom.root(),requests=[],base="https://reading.test/reading.manifest.json";
  const fetch=async url=>{
    const value=new URL(url);assert.equal(value.origin,"https://reading.test","no actual cross-origin/network request is allowed in this fixture");
    const relative=decodeURIComponent(value.pathname.slice(1)),file=path.resolve(directory,relative);
    assert(file.startsWith(directory+path.sep));
    const raw=fs.readFileSync(file,"utf8");requests.push({path:relative,bytes:Buffer.byteLength(raw)});
    const data=respond?await respond(relative,JSON.parse(raw)):JSON.parse(raw);
    return {ok:true,json:async()=>data};
  };
  vm.runInContext(code,vm.createContext({...dom,fetch,TextEncoder,URL,Map,Set,setTimeout,clearTimeout,console}));
  const reader=await dom.window.LitexReading.open(root,manifest,{baseUrl:base,locale:"en",onCheck:async()=>{if(!original)throw new Error("No verifier is attached to this component benchmark");return original;}});
  return {...dom,root,reader,requests,manifest};
}
async function run(){
  if(measure){
    const view=await open(),first=view.reader.getSelection().source,start=Date.now(),snapshot=await view.reader.getProjectSnapshot();
    const milliseconds=Date.now()-start;
    for(const source of snapshot.sources){
      let hash=0xcbf29ce484222325n;for(const byte of Buffer.from(source.content))hash=((hash^BigInt(byte))*0x100000001b3n)&0xffffffffffffffffn;
      assert.equal("fnv1a64:"+hash.toString(16).padStart(16,"0"),source.digest,"retained original source fingerprint");
    }
    const extra=view.requests.slice(1),paths=new Set(view.manifest.sources.filter(source=>source.id!==first).map(source=>source.source_url));
    assert(extra.every(request=>paths.has(request.path)));assert.equal(extra.length,paths.size);
    const bytes=extra.reduce((sum,request)=>sum+request.bytes,0),previous=view.manifest.sources.filter(source=>source.id!==first).reduce((sum,source)=>sum+fs.statSync(path.join(directory,source.chunk_url)).size,0);
    const longest=Array.from(snapshot.sources).filter(source=>source.id!==first).sort((a,b)=>b.content.length-a.content.length)[0];
    const statement=view.manifest.statements.find(item=>item.source_id===longest.id);assert(statement);
    const navigateStart=Date.now();await view.reader.selectStatement(statement.id);const navigateMilliseconds=Date.now()-navigateStart;
    assert(view.requests.some(request=>request.path===longest.chunk_url));assert.equal(view.root.querySelector(".lr-ide-input").value,longest.content);
    view.reader.destroy();
    console.log(JSON.stringify({passed:true,sources:snapshot.sources.length,sourceFingerprintsMatch:true,
      snapshotBytes:bytes,previousRequiredProofBytes:previous,offlineSnapshotMilliseconds:milliseconds,
      longestChapter:longest.path,longestChapterLines:longest.content.split("\n").length,
      offlineChapterOpenMilliseconds:navigateMilliseconds,proofStillLoadedOnDemand:true},null,2));return;
  }
  assert(original.sources.length>=3,"use the real three-chapter book or a larger actual book");
  const modern=await open(),before=modern.reader.getSelection(),first=modern.manifest.sources.find(source=>source.id===before.source);
  assert.equal(modern.requests.length,1);assert.equal(modern.requests[0].path,first.chunk_url);
  const [snapshot,parallel]=await Promise.all([modern.reader.getProjectSnapshot(),modern.reader.getProjectSnapshot()]);
  assert.deepEqual(snapshot,parallel);assert.equal(snapshot.sources.length,original.sources.length);assert.equal(snapshot.strict,true);
  assert.deepEqual(snapshot.configurations,original.configurations);
  for(const source of snapshot.sources)assert.equal(source.content,original.sources.find(item=>item.id===source.id).content);
  const sourceRequests=modern.requests.filter(request=>modern.manifest.sources.some(source=>source.source_url===request.path));
  assert.equal(sourceRequests.length,original.sources.length-1,"concurrent snapshots share each lightweight fetch");
  assert.deepEqual(modern.reader.getSelection(),before,"preparing source must not navigate or load proof into the reader");
  assert.equal(modern.requests.filter(request=>modern.manifest.sources.some(source=>source.chunk_url===request.path)).length,1);
  await modern.reader.getProjectSnapshot();assert.equal(modern.requests.length,original.sources.length,"source text is cached only within this opened document");
  const target=modern.manifest.sources.findLast(source=>source.id!==before.source),statement=original.statements.find(item=>item.source_id===target.id);
  await modern.reader.selectStatement(statement.id);
  assert(modern.requests.some(request=>request.path===target.chunk_url),"source-only preparation must not masquerade as loaded chapter proof");
  assert.equal(modern.reader.getSelection().source,target.id);
  assert.equal(modern.root.querySelector(".lr-ide-input").value,original.sources.find(source=>source.id===target.id).content);
  const modernBytes=sourceRequests.reduce((sum,item)=>sum+item.bytes,0);modern.reader.destroy();

  const legacy=await open({legacy:true});const previous=legacy.reader.getSelection();
  const oldSnapshot=await legacy.reader.getProjectSnapshot();
  assert.deepEqual(Array.from(oldSnapshot.sources,source=>source.content),original.sources.map(source=>source.content));
  assert.equal(legacy.requests.length,original.sources.length,"older exports retain the full-chunk fallback");
  assert.deepEqual(legacy.reader.getSelection(),previous);
  const legacyBytes=legacy.requests.slice(1).reduce((sum,item)=>sum+item.bytes,0);legacy.reader.destroy();
  assert(modernBytes<legacyBytes,"source-only snapshots must transfer less data than proof chapters");

  for(const kind of ["wrongManifest","wrongSource","wrongPath","missingContent","network"]){
    let firstAttempt=true;
    const view=await open({respond(relative,data){
      if(data.kind==="reading_source"&&firstAttempt){firstAttempt=false;
        if(kind==="wrongManifest")data.manifest_id="another-snapshot";
        if(kind==="wrongSource")data.source.id="another-source";
        if(kind==="wrongPath")data.source.path="another.lit";
        if(kind==="missingContent")delete data.source.content;
        if(kind==="network")throw new Error("source transport unavailable");
      }
      return data;
    }});
    const selection=view.reader.getSelection();await assert.rejects(view.reader.getProjectSnapshot());
    assert.deepEqual(view.reader.getSelection(),selection);const retried=await view.reader.getProjectSnapshot();
    assert.deepEqual(Array.from(retried.sources,source=>source.content),original.sources.map(source=>source.content),kind+" can retry after the bad part");view.reader.destroy();
  }
  const origin=await open({changeManifest(manifest){const first=manifest.entry_source_id||manifest.sources[0].id;manifest.sources.find(source=>source.id!==first).source_url="https://outside.example/source.json";}});
  await assert.rejects(origin.reader.getProjectSnapshot(),/share the manifest origin/);origin.reader.destroy();

  for(const action of ["update","destroy"]){
    const waiting=deferred(),started=deferred();
    const view=await open({async respond(relative,data){if(data.kind==="reading_source"){started.resolve();await waiting.promise;}return data;}});
    const snapshot=view.reader.getProjectSnapshot();await started.promise;
    if(action==="update")view.reader.update(original);else view.reader.destroy();
    const rejected=assert.rejects(snapshot,/opened document changed/);waiting.resolve();await rejected;
    if(action==="update")view.reader.destroy();
  }
  const destination=original.sources.at(-1),middle=original.sources[1],waiting=deferred(),started=deferred();let failMiddle=true;
  const editing=await open({async respond(relative,data){
    if(data.kind==="reading_chunk"&&data.source_id===destination.id){started.resolve();await waiting.promise;}
    if(data.kind==="reading_chunk"&&data.source_id===middle.id&&failMiddle){failMiddle=false;throw new Error("chapter transport unavailable");}
    return data;
  }});
  const initialSource=editing.reader.getSelection().source,entry=original.statements.find(item=>item.source_id===destination.id),moving=editing.reader.selectStatement(entry.id);
  await started.promise;const draft=editing.root.querySelector(".lr-ide-input");draft.value+="\n# changed while loading";draft.setSelectionRange(draft.value.length,draft.value.length);await draft.trigger("input");
  waiting.resolve();assert.equal(await moving,false);assert.equal(editing.reader.getSelection().source,initialSource);
  assert.equal(editing.reader.getSelection().statement,null,"a background merge cannot revive an old semantic selection");assert(!editing.root.querySelector(".lr-operation-status"));
  await editing.root.querySelectorAll("button.lr-chapter")[original.sources.length-1].click();
  assert.equal(editing.root.querySelector(".lr-ide-input").dataset.sourcePath,destination.path);
  assert.equal(editing.root.querySelectorAll(".lr-chain-equality,.lr-inline-inferences").length,0);
  await editing.root.querySelectorAll("button.lr-chapter")[1].click();
  assert(editing.root.querySelector(".lr-operation-status").textContent.includes("chapter transport unavailable"),"a load error stays visible while a draft is pending");
  await editing.root.querySelectorAll("button.lr-chapter")[1].click();
  assert.equal(editing.root.querySelector(".lr-ide-input").dataset.sourcePath,middle.path,"rendering a pending draft does not cancel a new chapter navigation");
  assert(!editing.root.querySelector(".lr-operation-status"));assert.equal(editing.reader.getSelection().fact,null);editing.reader.destroy();
  for(const fullDocument of [false,true]){
    const searching=await open();if(fullDocument)searching.reader.update(original);
    let query=searching.root.querySelector('.lr-book-search input');query.value='x > 0';await query.trigger('input');await new Promise(setImmediate);
    assert(searching.root.querySelectorAll('.lr-book-result').some(node=>node.querySelector('code').textContent.trim()==='x > 0'));
    const input=searching.root.querySelector('.lr-ide-input'),old=input.value;
    input.value='# 草稿\n'+old.replace('x > 0','x > 314159');input.setSelectionRange(input.value.length,input.value.length);await input.trigger('input');await new Promise(setImmediate);
    assert.equal(searching.root.querySelectorAll('.lr-book-result').length,0,'editing refreshes active search and removes replaced source text');
    query.value='314159';await query.trigger('input');await new Promise(setImmediate);
    let hits=searching.root.querySelectorAll('.lr-book-result');assert.equal(hits.length,1,'search finds the current draft text');
    assert(hits[0].textContent.includes('Source line 3'),'inserted source lines are reflected in search results');await hits[0].click();
    assert.equal(searching.reader.getSelection().focusLine,3);assert.equal(searching.reader.getSelection().statement,null,'draft hits do not select stale proof statements');
    await searching.root.querySelectorAll('button.lr-chapter')[1].click();await new Promise(setImmediate);
    hits=searching.root.querySelectorAll('.lr-book-result');assert.equal(hits.length,1,'a draft remains searchable after changing chapters');await hits[0].click();
    assert.equal(searching.root.querySelector('.lr-ide-input').value,'# 草稿\n'+old.replace('x > 0','x > 314159'));
    await searching.root.querySelector('.lr-restore').click();await new Promise(setImmediate);
    assert.equal(searching.root.querySelectorAll('.lr-book-result').length,0,'restoration removes the replaced draft text from active search');
    query=searching.root.querySelector('.lr-book-search input');query.value='x > 0';await query.trigger('input');await new Promise(setImmediate);
    assert(searching.root.querySelector('.lr-book-result').textContent.includes('Source line 2'),'restoration uses the original source line');
    assert.equal(searching.reader.getSelection().fact,null);searching.reader.destroy();
  }
  const searchGate=deferred(),searchStarted=deferred(),loadingSearch=await open({async respond(relative,data){if(data.kind==='reading_search'){searchStarted.resolve();await searchGate.promise;}return data;}});
  const searchBox=loadingSearch.root.querySelector('.lr-book-search input');searchBox.value='314159';await searchBox.trigger('input');await searchStarted.promise;
  const working=loadingSearch.root.querySelector('.lr-ide-input');working.value=working.value.replace('x > 0','x > 314159');await working.trigger('input');
  searchGate.resolve();await new Promise(setImmediate);assert.equal(loadingSearch.root.querySelectorAll('.lr-book-result').length,1,'a delayed retained search index cannot overwrite newer draft text');loadingSearch.reader.destroy();
  const predicate=await open({changeManifest(manifest){manifest.entry_source_id=manifest.sources[1].id;}}),predicateSource=predicate.reader.getSelection().source;
  const input=predicate.root.querySelector('.lr-ide-input'),token=predicate.root.querySelector('.lr-token.lr-syntax-predicate');assert(token);input.focus();predicate.document.elementFromPoint=()=>token;
  await input.trigger('pointermove',{clientX:100,clientY:80});await new Promise(resolve=>setTimeout(resolve,480));
  const definition=predicate.root.querySelector('.lr-proof-popover .lr-predicate-definition');assert(definition&&definition.textContent.includes('above_zero(x)'),'predicate hover resolves the actual declaration in an exported book');assert.equal(predicate.reader.getSelection().source,predicateSource);assert.equal(predicate.document.activeElement,input,'loading a declaration in place does not steal editing focus');predicate.reader.destroy();
  console.log(JSON.stringify({passed:true,sources:original.sources.length,lightweightSnapshotBytes:modernBytes,
    previousFullChunkBytes:legacyBytes,sourceBytesMatch:true,concurrentFetchesShared:true,
    proofRemainsLazy:true,legacyCompatible:true,badPartAndNetworkRetries:true,
    crossOriginPartsRejected:true,documentChangeAndDestroyCancel:true,
    editingCancelsOlderNavigation:true,newDraftNavigationAndFailureRetryWork:true,currentDraftSearchAndExactLine:true,predicateDefinitionInBook:true},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
