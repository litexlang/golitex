(function () {
  "use strict";
  const initial=JSON.parse(document.getElementById("reading-data").textContent);
  const live=document.body.dataset.live==="true";
  const language=document.getElementById("language");
  language.value=(initial.language||"en").startsWith("zh")?"zh":"en";
  const status=document.getElementById("upload-status");
  const fileInput=document.getElementById("source-files");
  const folderInput=document.getElementById("project-files");
  const parentOrigin=(()=>{try{return document.referrer?new URL(document.referrer).origin:null;}catch{return null;}})();
  const reader=window.LitexReading.mount(document.getElementById("reader"),{
    document:initial,locale:language.value,
    onNavigate(selection){if(parentOrigin&&window.parent!==window)window.parent.postMessage({type:"litex-reading:selection",selection},parentOrigin);}
  });
  const chooseFiles=document.getElementById("choose-files");
  const chooseProject=document.getElementById("choose-project");
  document.getElementById("upload-actions").hidden=false;
  chooseProject.hidden=!live;
  if(!live)fileInput.accept=".json";
  function labels(){const zh=language.value==="zh";chooseFiles.textContent=live?(zh?"打开文件":"Open files"):(zh?"打开阅读 JSON":"Open reading JSON");chooseProject.textContent=zh?"打开项目文件夹":"Open project folder";document.getElementById("language-label").textContent=zh?"语言":"Language";document.documentElement.lang=zh?"zh-CN":"en";document.body.dataset.dropLabel=live?(zh?"拖入 Litex 文件或项目文件夹":"Drop Litex files or a project folder"):(zh?"拖入阅读 JSON":"Drop a reading JSON bundle");}
  labels();
  language.addEventListener("change",()=>{labels();reader.setLanguage(language.value);});
  chooseFiles.addEventListener("click",()=>fileInput.click());
  chooseProject.addEventListener("click",()=>folderInput.click());
  fileInput.addEventListener("change",()=>upload([...fileInput.files].map(file=>({file,path:file.webkitRelativePath||file.name}))));
  folderInput.addEventListener("change",()=>upload([...folderInput.files].map(file=>({file,path:file.webkitRelativePath||file.name}))));
  window.addEventListener("message",event=>{
    if(!parentOrigin||event.origin!==parentOrigin||event.source!==window.parent)return;
    if(event.data?.type==="litex-reading:select"&&typeof event.data.statement_id==="string")reader.selectStatement(event.data.statement_id);
  });
  function report(message,error=false){status.textContent=message;status.dataset.error=String(error);}
  async function upload(entries){
    if(!entries.length)return;
    const zh=language.value==="zh";
    chooseFiles.disabled=true;chooseProject.disabled=true;
    try{
      if(entries.length===1&&entries[0].path.endsWith(".json")){
        const data=JSON.parse(await entries[0].file.text());
        if(data.kind!=="reading"||data.schema_version!=="1"||!Array.isArray(data.sources)||!Array.isArray(data.statements))throw new Error(zh?"这不是受支持的阅读数据包。":"This is not a supported reading bundle.");
        reader.update(data);report("");return;
      }
      if(!live)throw new Error(zh?"本页面可读取已有阅读 JSON；验证新源码请使用 litex -reading。":"This page reads saved bundles. Use litex -reading to verify new source.");
      entries=entries.filter(entry=>entry.path.endsWith(".lit")||entry.path.split("/").at(-1)==="litex.config");
      if(!entries.length)throw new Error(zh?"请选择 .lit 文件或包含 litex.config 的项目。":"Choose .lit files or a project containing litex.config.");
      if(entries.length>512)throw new Error(zh?"一次最多打开 512 个源码与配置文件。":"At most 512 source/config files can be opened at once.");
      if(entries.reduce((sum,entry)=>sum+entry.file.size,0)>8*1024*1024)throw new Error(zh?"源码与配置总大小不能超过 8 MiB。":"Source/config input must not exceed 8 MiB.");
      report(zh?"正在验证并生成阅读数据…":"Verifying and preparing the reading data…");
      const files=await Promise.all(entries.map(async entry=>({path:entry.path,content:await entry.file.text()})));
      const response=await fetch("api/reading/build",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({files,language:language.value})});
      const data=await response.json();
      if(data.kind!=="reading")throw new Error(data.error||"Reading build failed");
      reader.update(data);report(data.run_result==="success"?"":(zh?"部分源码未通过验证；可查看已接受的步骤与失败原因。":"Some source was not accepted. Inspect the accepted steps and diagnostics."),data.run_result!=="success");
    }catch(error){report(error.message,true);}finally{chooseFiles.disabled=false;chooseProject.disabled=false;fileInput.value="";folderInput.value="";}
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
