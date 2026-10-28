"use strict";
// Run the real shell and reader together, without browser or network access.
const fs=require("node:fs"),path=require("node:path"),vm=require("node:vm"),assert=require("node:assert/strict");
const {createDOM}=require("./dom.cjs");
const directory=process.argv[2];
if(!directory)throw new Error("Usage: node src/reading/web/tests/app.cjs <fixture-directory>");
const readerCode=fs.readFileSync(path.join(__dirname,"../reader.js"),"utf8"),appCode=fs.readFileSync(path.join(__dirname,"../app.js"),"utf8");
function fixture(name){return JSON.parse(fs.readFileSync(path.join(directory,name+".json"),"utf8"));}
async function open(options={}){
  const dom=createDOM(),initial=options.initial||fixture("definition"),document=dom.document;
  const node=(tag,id,text="")=>{const value=document.createElement(tag);value.id=id;value.textContent=text;document.body.append(value);return value;};
  node("script","reading-data",JSON.stringify(initial));node("select","language");node("label","language-label");
  node("div","upload-status");node("input","source-files");node("input","project-files");const root=node("main","reader");
  node("script","reading-build-endpoint","/api/reading/build");
  const alternate=node("link","english-source");alternate.setAttribute("rel","alternate");alternate.setAttribute("hreflang","en");alternate.setAttribute("href",options.alternate||"../../en/definitions/index.html");
  node("script","reading-example-groups",JSON.stringify([{titles:{zh:"从这里读起",en:"Start reading"},items:[
    {titles:{zh:"定义与实例",en:"Definitions and instances"},hrefs:{zh:"lessons/zh/definitions/",en:"lessons/en/definitions/"}},
    {titles:{en:"Legacy",zh:"旧链接"},href:"cases/example/"},
    {titles:{en:"Unsafe",zh:"无效链接"},hrefs:{zh:"javascript:alert(1)",en:"https://outside.example/"}}
  ]}]));
  const assigned=[],requests=[],href="http://reading.test/lessons/zh/definitions/?lang=zh",location={href,search:"?lang=zh",origin:"http://reading.test",assign(url){assigned.push(url);}};
  if(options.file)dom.window.location={protocol:"file:"};
  const fetch=async(url,request)=>{requests.push({url,...request});return {ok:true,json:async()=>JSON.parse(JSON.stringify(initial))};};
  const context=vm.createContext({...dom,TextEncoder,URL,URLSearchParams,Map,Set,setTimeout,clearTimeout,console,location,fetch});
  vm.runInContext(readerCode,context);
  let reader;
  const original=dom.window.LitexReading;
  dom.window.LitexReading={...original,mount(...args){reader=original.mount(...args);return reader;}};
  await vm.runInContext(appCode,context);
  return {...dom,root,reader,requests,assigned,initial,async language(value){const select=document.getElementById("language");select.value=value;await select.trigger("change");}};
}
async function run(){
  let page=await open();
  assert.equal(page.reader.hasLocalEdits(),false);
  const menu=page.root.querySelectorAll(".lr-extra-examples a");
  assert(menu.some(link=>link.href==="lessons/zh/definitions/?lang=zh"));assert(menu.some(link=>link.href==="cases/example/?lang=zh"));
  assert(!menu.some(link=>link.textContent==="无效链接"));
  await page.language("en");assert.deepEqual(page.assigned,["http://reading.test/lessons/en/definitions/index.html?lang=en"]);page.reader.destroy();

  page=await open({file:true});assert(page.root.querySelectorAll(".lr-extra-examples a").some(link=>link.href==="lessons/zh/definitions/index.html?lang=zh"));page.reader.destroy();

  page=await open();const input=page.root.querySelector(".lr-ide-input");input.value+="\n# keep this edit";await input.trigger("input");
  assert(page.reader.hasLocalEdits());await page.language("en");
  assert.deepEqual(page.assigned,[]);assert(page.root.querySelector(".lr-ide-input").value.endsWith("# keep this edit"));
  assert(page.document.getElementById("upload-status").textContent.includes("edited source is kept"));
  assert(page.root.querySelectorAll(".lr-extra-examples a").some(link=>link.href==="lessons/en/definitions/?lang=en"));
  await page.root.querySelector(".lr-restore").click();assert(!page.reader.hasLocalEdits());page.reader.destroy();

  page=await open();page.reader.update(fixture("sets"));await page.language("en");
  assert.deepEqual(page.assigned,[],"alternate metadata must not navigate away from a different opened document");page.reader.destroy();
  page=await open({alternate:"https://outside.example/lesson/"});await page.language("en");
  assert.deepEqual(page.assigned,[],"alternate source pages must share the current origin");page.reader.destroy();

  page=await open();await page.root.querySelector(".lr-check").click();
  assert.equal(page.requests.length,1,page.root.querySelector(".lr-editor-error")?.textContent);assert.equal(page.requests[0].url,"/api/reading/build");
  const body=JSON.parse(page.requests[0].body);assert.equal(body.entry.kind,"file");assert.equal(body.strict,true);
  assert(body.files.some(file=>file.content===page.initial.sources[0].content),"the checking host receives the retained source, not proof JSON");
  const config=body.files.find(file=>file.path==="litex.config").content;
  assert.equal(config.split("\n").filter(line=>line.includes(" = ")).length,page.initial.sources.length,"a retained prefix does not require later chapters");
  page.reader.destroy();

  const incomplete=fixture("definition");incomplete.sources.shift();page=await open({initial:incomplete});
  await page.root.querySelector(".lr-check").click();assert.equal(page.requests.length,0);
  assert(page.root.querySelector(".lr-editor-error").textContent.includes("教材依赖不完整"));page.reader.destroy();

  page=await open({initial:fixture("book")});await page.root.querySelector(".lr-check").click();
  assert.equal(page.requests.length,1);
  const complete=JSON.parse(page.requests[0].body).files.find(file=>file.path==="litex.config").content;
  assert.equal(complete.split("\n").filter(line=>line.includes(" = ")).length,3,"a complete book retains its full configuration");page.reader.destroy();
  console.log(JSON.stringify({passed:true,localeMenuPaths:true,legacyMenuLinks:true,unsafeLinksExcluded:true,
    alternateSourceNavigation:true,editedSourcePreserved:true,openedDocumentPreserved:true,
    crossOriginAlternatesIgnored:true,checkingPayloadUsesActualSource:true,
    prefixOnlyChecks:true,missingPredecessorRejected:true,completeBookPreserved:true},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
