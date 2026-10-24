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
  const options={
    locale:language.value,
    exampleGroups:JSON.parse(document.getElementById("reading-example-groups")?.textContent||"[]"),
    onOpenFiles:()=>fileInput.click(),
    onOpenProject:live?()=>folderInput.click():undefined,
    onNavigate(selection,metadata){if(parentOrigin&&window.parent!==window)window.parent.postMessage({type:"litex-reading:selection",selection,...metadata},parentOrigin);}
  };
  let reader;
  try{reader=initial.kind==="reading_manifest"?await window.LitexReading.open(document.getElementById("reader"),initial,{...options,baseUrl:location.href}):window.LitexReading.mount(document.getElementById("reader"),{...options,document:initial});}
  catch(error){status.textContent=error.message;status.dataset.error="true";reader=window.LitexReading.mount(document.getElementById("reader"),{...options,document:{sources:[],statements:[],rules:[]}});}
  if(!live)fileInput.accept=".json";
  function labels(){const zh=language.value==="zh";document.getElementById("language-label").textContent=zh?"语言":"Language";document.documentElement.lang=zh?"zh-CN":"en";document.body.dataset.dropLabel=live?(zh?"把自己的文件放到这里":"Drop your files here"):(zh?"把阅读记录放到这里":"Drop reading records here");}
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
        reader.update(data);report("");return;
      }
      if(!live)throw new Error(zh?"这里可以打开已保存的阅读记录（.json）。检查自己的 Litex 原文，请在电脑上运行 litex -reading。":"Open saved reading records (.json) here. To check your own Litex source, run litex -reading on your computer.");
      entries=entries.filter(entry=>entry.path.endsWith(".lit")||["litex.config","reading-titles.json"].includes(entry.path.split("/").at(-1)));
      if(!entries.length)throw new Error(zh?"请选择 .lit 文件或包含 litex.config 的项目。":"Choose .lit files or a project containing litex.config.");
      if(entries.length>512)throw new Error(zh?"一次最多打开 512 个源码与配置文件。":"At most 512 source/config files can be opened at once.");
      if(entries.reduce((sum,entry)=>sum+entry.file.size,0)>8*1024*1024)throw new Error(zh?"源码与配置总大小不能超过 8 MiB。":"Source/config input must not exceed 8 MiB.");
      report(zh?"正在验证并生成阅读数据…":"Verifying and preparing the reading data…");
      const files=await Promise.all(entries.map(async entry=>({path:entry.path,content:await entry.file.text()})));
      const response=await fetch("api/reading/build",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({files,language:language.value})});
      const data=await response.json();
      if(data.kind!=="reading")throw new Error(data.error||"Reading build failed");
      reader.update(data);report(data.run_result==="success"?"":(zh?"部分源码未通过验证；可查看已接受的步骤与失败原因。":"Some source was not accepted. Inspect the accepted steps and diagnostics."),data.run_result!=="success");
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
