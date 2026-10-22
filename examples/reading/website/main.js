(async function () {
  "use strict";
  const status=document.getElementById("selection-status");
  const frame=document.getElementById("frame-reader");
  const conclusionButton=document.getElementById("select-conclusion");
  const inferredButton=document.getElementById("select-inferred");
  const wdButton=document.getElementById("select-wd");
  try {
    const manifestUrl=new URL("book/reading.manifest.json",location.href);
    const response=await fetch(manifestUrl,{cache:"no-store"});
    if(!response.ok)throw new Error("无法读取 book/reading.manifest.json；请先按 README 生成静态导出。");
    const readingJson=await response.json();
    const statements=new Map(readingJson.statements.map(value=>[value.id,value]));
    const facts=new Map(readingJson.facts.map(value=>[value.id,value]));
    const wellDefinedness=new Map((readingJson.well_definedness||[]).map(value=>[value.id,value]));
    function report(kind,selection){
      const fact=facts.get(selection.fact);
      const statement=statements.get(selection.statement);
      const wd=wellDefinedness.get(selection.wd);
      status.textContent=kind+"："+(wd?"有定义 "+wd.object:fact?"事实 "+fact.text:"源码行 "+(statement?.line||"—"));
    }
    const reader=await LitexReading.open(document.getElementById("component-reader"),readingJson,{
      baseUrl:manifestUrl.href,locale:"zh",onNavigate:selection=>report("组件",selection)
    });
    const conclusion=readingJson.statements.filter(value=>value.status==="accepted"&&value.source_id===readingJson.entry_source_id).at(-1);
    // Choose by actual citation/producer IDs; spelling is never an edge.
    const inferredId=(conclusion?.cited_fact_ids||[]).find(id=>facts.get(id)?.inference_ids?.length)
      ||readingJson.statements.flatMap(value=>value.inferred_fact_ids||[])[0];
    const wdId=(conclusion?.well_definedness_ids||[]).find(id=>wellDefinedness.get(id)?.producer_statement_id)
      ||[...wellDefinedness.values()].find(value=>value.producer_statement_id)?.id;
    conclusionButton.addEventListener("click",()=>{
      reader.selectStatement(conclusion.id);
      frame.contentWindow.postMessage({type:"litex-reading:select",bundle_id:reader.getBundleId(),statement_id:conclusion.id},location.origin);
    });
    inferredButton.addEventListener("click",()=>{
      reader.selectFact(inferredId);
      frame.contentWindow.postMessage({type:"litex-reading:select",bundle_id:reader.getBundleId(),fact_id:inferredId},location.origin);
    });
    wdButton.addEventListener("click",()=>{
      reader.selectWellDefinedness(wdId);
      frame.contentWindow.postMessage({type:"litex-reading:select",bundle_id:reader.getBundleId(),well_definedness_id:wdId},location.origin);
    });
    window.addEventListener("message",event=>{
      if(event.origin!==location.origin||event.source!==frame.contentWindow)return;
      if(!["litex-reading:ready","litex-reading:selection"].includes(event.data?.type))return;
      if(event.data.bundle_id!==reader.getBundleId()){
        conclusionButton.disabled=true;inferredButton.disabled=true;wdButton.disabled=true;
        status.textContent="iframe 已切换数据；请重新载入宿主网页以同步。";
        return;
      }
      if(event.data.type==="litex-reading:selection")report("iframe",event.data.selection);
      else {
        conclusionButton.disabled=!conclusion;
        inferredButton.disabled=!inferredId;
        wdButton.disabled=!wdId;
        status.textContent="组件与 iframe 已就绪";
      }
    });
    frame.src="book/index.html?build="+encodeURIComponent(reader.getBundleId());
  } catch(error) {
    status.textContent="加载失败";
    document.getElementById("host-error").textContent=error.message;
  }
})();
