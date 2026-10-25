(async function () {
  "use strict";
  const initial=JSON.parse(document.getElementById("reading-data").textContent);
  const live=document.body.dataset.live==="true";
  const language=document.getElementById("language");
  const requestedLanguage=new URLSearchParams(location.search).get("lang");
  language.value=["zh","en"].includes(requestedLanguage)?requestedLanguage:(initial.language||"en").startsWith("zh")?"zh":"en";
  const status=document.getElementById("upload-status");
  const fileInput=document.getElementById("source-files");
  const folderInput=document.getElementById("project-files");
  const parentOrigin=(()=>{try{return document.referrer?new URL(document.referrer).origin:null;}catch{return null;}})();
  let projectSnapshot=null;
  const buildEndpoint=live?"/api/reading/build":document.getElementById("reading-build-endpoint")?.textContent.trim();
  async function checkSource({changes,sourcePath,locale}){
    const snapshot=projectSnapshot||(projectSnapshot=reader.getProjectSnapshot());
    let project;
    try{project=await snapshot;}catch(error){if(projectSnapshot===snapshot)projectSnapshot=null;throw error;}
    const configs=project.configurations;
    if(configs.length>1||configs.some(item=>item.configuration.imports?.length))throw new Error(locale==="zh"?"此项目包含额外模块依赖，请先用完整项目打开；当前编辑检查支持独立文件和单配置教材。":"This project has module dependencies. Open the complete project; inline checking currently supports single-configuration books and independent files.");
    const files=project.sources.map(source=>({path:source.path,content:changes[source.path]??source.content}));
    if(files.some(file=>typeof file.content!=="string"))throw new Error("Source snapshot is incomplete");
    const exports=configs[0]?.configuration.exports||[];
    if(exports.length){
      if(exports.some(item=>!files.some(file=>file.path===item.path)))throw new Error(locale==="zh"?"教材依赖不完整，未开始检查。":"Book dependencies are incomplete; nothing was checked.");
      files.push({path:"litex.config",content:"[export]\n"+exports.map(item=>item.name+" = "+JSON.stringify("./"+item.path)).join("\n")+"\n"});
    }
    const titles={};for(const source of project.sources)if(source.titles)titles[source.path]=source.titles;
    files.push({path:"reading-titles.json",content:JSON.stringify({kind:"reading_titles",sources:titles})});
    const response=await fetch(buildEndpoint,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({files,entry:{kind:"file",path:sourcePath},language:locale,strict:project.strict})});
    const result=await response.json();
    if(!response.ok||result.kind!=="reading")throw new Error(result.error||"Reading check failed");
    // A failed prefix may never execute later chapters. Retain only their
    // authored source for navigation/editing, without any old proof or symbols.
    const returnedPaths=new Set(result.sources.map(source=>source.path));
    for(const source of project.sources)if(!returnedPaths.has(source.path))result.sources.push({id:"editor-source:"+source.path,path:source.path,content:changes[source.path]??source.content,titles:source.titles,role:source.role,editor_unchecked:true});
    return result;
  }
  const options={
    locale:language.value,
    onCheck:buildEndpoint?checkSource:undefined,
    exampleGroups:JSON.parse(document.getElementById("reading-example-groups")?.textContent||"[]"),
    onOpenFiles:()=>fileInput.click(),
    onOpenProject:buildEndpoint?()=>folderInput.click():undefined,
    onNavigate(selection,metadata){if(parentOrigin&&window.parent!==window)window.parent.postMessage({type:"litex-reading:selection",selection,...metadata},parentOrigin);}
  };
  let reader;
  try{reader=initial.kind==="reading_manifest"?await window.LitexReading.open(document.getElementById("reader"),initial,{...options,baseUrl:location.href}):window.LitexReading.mount(document.getElementById("reader"),{...options,document:initial});}
  catch(error){status.textContent=error.message;status.dataset.error="true";reader=window.LitexReading.mount(document.getElementById("reader"),{...options,document:{sources:[],statements:[],rules:[]}});}
  if(!buildEndpoint)fileInput.accept=".json";
  function labels(){const zh=language.value==="zh";document.getElementById("language-label").textContent=zh?"语言":"Language";document.documentElement.lang=zh?"zh-CN":"en";document.body.dataset.dropLabel=buildEndpoint?(zh?"把自己的文件放到这里":"Drop your files here"):(zh?"把阅读记录放到这里":"Drop reading records here");}
  labels();
  language.addEventListener("change",()=>{labels();reader.setLanguage(language.value);});
  fileInput.addEventListener("change",()=>upload([...fileInput.files].map(file=>({file,path:file.webkitRelativePath||file.name}))));
  folderInput.addEventListener("change",()=>upload([...folderInput.files].map(file=>({file,path:file.webkitRelativePath||file.name}))));
  window.addEventListener("message",event=>{
    if(!parentOrigin||event.origin!==parentOrigin||event.source!==window.parent)return;
    if(event.data?.type==="litex-reading:select"){
      if(typeof event.data.bundle_id==="string"&&event.data.bundle_id!==reader.getBundleId())return;
      if(typeof event.data.well_definedness_id==="string")reader.selectWellDefinedness(event.data.well_definedness_id);
      else if(typeof event.data.fact_id==="string")reader.selectFact(event.data.fact_id);
      else if(typeof event.data.statement_id==="string")reader.selectStatement(event.data.statement_id);
    }
  });
  if(parentOrigin&&window.parent!==window)window.parent.postMessage({type:"litex-reading:ready",bundle_id:reader.getBundleId(),selection:reader.getSelection()},parentOrigin);
  function report(message,error=false){status.textContent=message;status.dataset.error=String(error);}
  async function upload(entries){
    if(!entries.length)return;
    const zh=language.value==="zh";
    fileInput.disabled=true;folderInput.disabled=true;
    try{
      if(entries.length===1&&entries[0].path.endsWith(".json")){
        const data=JSON.parse(await entries[0].file.text());
        if(data.kind!=="reading"||!["1","2"].includes(data.schema_version)||!Array.isArray(data.sources)||!Array.isArray(data.statements))throw new Error(zh?"这份文件不是可打开的阅读记录。":"This file does not contain supported reading records.");
        projectSnapshot=null;reader.update(data);report("");return;
      }
      if(!buildEndpoint)throw new Error(zh?"这里可以打开已保存的阅读记录（.json）。检查自己的 Litex 原文，请在电脑上运行 litex -reading。":"Open saved reading records (.json) here. To check your own Litex source, run litex -reading on your computer.");
      entries=entries.filter(entry=>entry.path.endsWith(".lit")||["litex.config","reading-titles.json"].includes(entry.path.split("/").at(-1)));
      if(!entries.length)throw new Error(zh?"请选择 .lit 文件或包含 litex.config 的项目。":"Choose .lit files or a project containing litex.config.");
      if(entries.length>512)throw new Error(zh?"一次最多打开 512 个源码与配置文件。":"At most 512 source/config files can be opened at once.");
      if(entries.reduce((sum,entry)=>sum+entry.file.size,0)>8*1024*1024)throw new Error(zh?"源码与配置总大小不能超过 8 MiB。":"Source/config input must not exceed 8 MiB.");
      report(zh?"正在验证并生成阅读数据…":"Verifying and preparing the reading data…");
      const files=await Promise.all(entries.map(async entry=>({path:entry.path,content:await entry.file.text()})));
      const response=await fetch(buildEndpoint,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({files,language:language.value})});
      const data=await response.json();
      if(data.kind!=="reading")throw new Error(data.error||"Reading build failed");
      projectSnapshot=null;reader.update(data);report(data.run_result==="success"?"":(zh?"部分源码未通过验证；可查看已接受的步骤与失败原因。":"Some source was not accepted. Inspect the accepted steps and diagnostics."),data.run_result!=="success");
    }catch(error){report(error.message,true);}finally{fileInput.disabled=false;folderInput.disabled=false;fileInput.value="";folderInput.value="";}
  }
  async function droppedEntry(entry,prefix=""){
    if(entry.isFile){const file=await new Promise((resolve,reject)=>entry.file(resolve,reject));return [{file,path:prefix+entry.name}];}
    if(entry.isDirectory){const reader=entry.createReader();let result=[];while(true){const children=await new Promise((resolve,reject)=>reader.readEntries(resolve,reject));if(!children.length)break;for(const child of children)result=result.concat(await droppedEntry(child,prefix+entry.name+"/"));}return result;}
    return [];
  }
  let dragDepth=0;
  document.addEventListener("dragenter",event=>{if(event.dataTransfer?.types.includes("Files")){event.preventDefault();dragDepth++;document.body.classList.add("reading-dropping");}});
  document.addEventListener("dragover",event=>{if(event.dataTransfer?.types.includes("Files"))event.preventDefault();});
  document.addEventListener("dragleave",()=>{if(--dragDepth<=0){dragDepth=0;document.body.classList.remove("reading-dropping");}});
  document.addEventListener("drop",async event=>{
    if(!event.dataTransfer?.files.length)return;
    event.preventDefault();dragDepth=0;document.body.classList.remove("reading-dropping");
    try{
      const items=[...event.dataTransfer.items];
      const entries=items.map(item=>item.webkitGetAsEntry?.()).filter(Boolean);
      if(entries.length){let files=[];for(const entry of entries)files=files.concat(await droppedEntry(entry));await upload(files);}
      else await upload([...event.dataTransfer.files].map(file=>({file,path:file.name})));
    }catch(error){report(error.message,true);}
  });
})();
