/* The same component is used by local preview, static export and host websites. */
(function (global) {
  "use strict";
  const copy = {
    en: { source:"Source", why:"Why it holds", verified:"Verified", failed:"Incomplete verification", accepted:"Accepted", rejected:"Not established", premise:"Actual grounds", rules:"Rules used", concepts:"Concepts", proof:"Explore the evidence", raw:"Inspect reading data", empty:"Follow the mathematics", emptyHint:"Open a .lit file or a complete Litex project to explore its statements, definitions and proof grounds.", definition:"Definition", references:"Occurrences", rulebook:"Rule Book", search:"Search rules", usedOnly:"Used in this book", noPremise:"This record has no earlier stored-fact citation.", unavailable:"Some reading information has not been exported.", catalogueOnly:"Catalogue identity; an authored description is not available in this bundle.", previous:"Previous", next:"Next", download:"Download JSON", back:"Back", selectedLegend:"Selected statement", premiseLegend:"Cited fact", noRules:"This statement does not use a builtin rule.", sourceLine:"Source line", noDefinition:"No source declaration is recorded in this bundle.", local:"Local proof context", engine:"Built with", uses:"Used here", notFalse:"A failed check does not prove the statement false." },
    zh: { source:"源码", why:"这句话为什么成立", verified:"验证通过", failed:"验证未全部通过", accepted:"已接受", rejected:"尚未建立", premise:"实际采用的依据", rules:"本次使用的规则", concepts:"相关概念", proof:"展开证明依据", raw:"查看阅读数据", empty:"沿着依据，读懂数学", emptyHint:"打开 .lit 文件或完整 Litex 项目，探索陈述、定义和证明依据之间的联系。", definition:"定义", references:"出现位置", rulebook:"规则手册", search:"搜索规则", usedOnly:"只看本书使用的规则", noPremise:"本条记录没有引用更早的已存事实。", unavailable:"部分阅读信息尚未导出。", catalogueOnly:"本条目记录了规则身份；数据包尚未提供完整说明。", previous:"上一页", next:"下一页", download:"下载 JSON", back:"返回", selectedLegend:"当前陈述", premiseLegend:"引用的事实", noRules:"本句没有使用内置规则。", sourceLine:"源码行", noDefinition:"数据包中没有记录对应的源码声明。", local:"局部证明上下文", engine:"构建内核", uses:"在这里使用", notFalse:"检查未通过，并不表示这句话为假。" }
  };
  Object.assign(copy.en,{title:"Interactive textbook",hint:"Select a statement to follow its grounds, or a concept to find its definition.",therefore:"Therefore",previousStep:"Previous",nextStep:"Next",occurrenceLegend:"Concept",notExported:"Execution evidence unavailable",outerProof:"Enclosing proof",context:"Context",sourceMappingGap:"Some nested execution results have no precise source mapping.",category:"Rule category",allCategories:"All categories",builtin:"Builtin rules",builtin_theorem:"Builtin theorems",infer:"Inference rules",user_trust:"User assumption",axiom:"Axiom",axiom_release:"Axiom application"});
  Object.assign(copy.zh,{title:"可交互教科书",hint:"点击陈述查看推导依据，点击概念查看定义与出现位置。",therefore:"因此",previousStep:"上一步",nextStep:"下一步",occurrenceLegend:"概念",notExported:"执行依据未导出",outerProof:"上一层证明",context:"上下文",sourceMappingGap:"部分内部执行结果尚无精确的源码映射。",category:"规则分类",allCategories:"全部分类",builtin:"内置规则",builtin_theorem:"内置定理",infer:"推导规则",user_trust:"用户假设",axiom:"公理",axiom_release:"公理应用"});
  Object.assign(copy.en,{declarations:"Definitions and theorems used",trust:"Assumptions and axioms",trustUsed:"This derivation depends on these explicit assumptions or axioms."});
  Object.assign(copy.zh,{declarations:"采用的定义与定理",trust:"假设与公理",trustUsed:"这条推导依赖以下显式假设或公理。"});
  Object.assign(copy.en,{inferred:"Inferred fact",inferredFacts:"Facts inferred here",inferredFrom:"Inferred from",producer:"Source statement"});
  Object.assign(copy.zh,{inferred:"推导事实",inferredFacts:"本句推导出的事实",inferredFrom:"由此推导",producer:"产生它的原语句"});
  Object.assign(copy.en,{fact:"Fact",hypothesis:"Local hypothesis",declaration:"Introduced by a declaration",verifiedFact:"Established fact",formation:"Formation evidence",hypothesisHint:"This fact is assumed inside the enclosing proof context.",declarationHint:"This fact is introduced by the object or parameter declaration.",factSourceGap:"This bundle has no source producer for this fact.",factProofGap:"Fact-specific evidence is unavailable; inspect its source statement."});
  Object.assign(copy.zh,{fact:"事实",hypothesis:"局部假设",declaration:"由声明引入",verifiedFact:"已建立的事实",formation:"表达式有定义的依据",hypothesisHint:"这条事实是所在证明上下文中的假设。",declarationHint:"这条事实由对象或参数的声明引入。",factSourceGap:"数据包尚未记录这条事实的来源语句。",factProofGap:"本条事实的独立依据尚未导出，可查看来源语句。"});
  Object.assign(copy.en,{wellDefined:"Well-defined expression",registration:"Registration",registrationHint:"The engine recorded this exact expression as well-defined in this scope.",registrationProof:"Its formation evidence is retained by the source statement.",wdGap:"Some well-definedness registrations have no exported source."});
  Object.assign(copy.zh,{wellDefined:"表达式有定义",registration:"登记记录",registrationHint:"内核在此作用域中登记了这个表达式有定义。",registrationProof:"其形成依据保留在来源语句中。",wdGap:"部分有定义登记尚未关联到导出的来源。"});
  Object.assign(copy.en,{book:"Contents and search",chapters:"Chapters",dependencies:"Dependencies",bookSearch:"Search all source",loading:"Loading chapter…",loadingIndex:"Loading search index…",noMatches:"No matches",sourceText:"Source text",noStatement:"This source line has no exported execution statement.",changedBuild:"The reading data changed. Reopen the book.",loadFailed:"Could not load reading data"});
  Object.assign(copy.zh,{book:"目录与搜索",chapters:"章节",dependencies:"依赖模块",bookSearch:"搜索全书源码",loading:"正在加载章节…",loadingIndex:"正在加载搜索索引…",noMatches:"没有匹配结果",sourceText:"源码文本",noStatement:"这行源码没有对应的执行语句记录。",changedBuild:"阅读数据已更新，请重新打开这本书。",loadFailed:"无法加载阅读数据"});
  const roles = { base_in_real_proof:["Real base", "底数属于实数"], nonnegative_addend_proof:["Nonnegative addend", "加项非负"], well_defined_proof:["Well-defined expressions", "表达式有定义"], well_defined:["Well-defined expressions", "表达式有定义"], searched_proof:["Selected proof", "采用的证明"], verify_result:["Verification grounds", "验证依据"], store_and_infer_result:["Established knowledge", "建立的知识"], store_and_infer:["Established knowledge", "建立的知识"], local_env:["Local context", "局部上下文"], introduced_params:["Introduced parameters", "引入的参数"], assumed_dom_facts:["Local hypotheses", "局部假设"], proved_then_facts:["Conclusions", "结论"], cite_fact_id:["Cited fact", "引用的事实"], source_fact_id:["Source fact", "来源事实"], fact:["Statement", "数学陈述"], statement:["Source statement", "源码陈述"], value:["Evidence", "依据"] };
  const routeNames = { ByKnownAtomicFact:["Earlier fact", "更早的事实"], ByKnownForallFact:["Earlier universal fact", "更早的全称事实"], ByEquivalenceClass:["Stored equalities", "已建立的等式"], ByLocalIntroduction:["Local proof", "局部证明"], ByBuiltinRule:["Builtin rule", "内置规则"], ByBuiltinStrategy:["Structured derivation", "结构化推导"], ByBuiltinRewrite:["Checked rewrite", "经过检查的改写"], Success:["Established", "已建立"], Failed:["Not established", "尚未建立"] };
  function element(tag, className, content) { const node=document.createElement(tag); if(className)node.className=className; if(content!==undefined)node.textContent=String(content); return node; }
  function button(label, className, callback) { const node=element("button",className,label); node.type="button"; node.addEventListener("click",callback); return node; }
  function array(value) { return Array.isArray(value)?value:[]; }
  function humanize(value) { return String(value||"").replace(/([a-z])([A-Z])/g,"$1 $2").replace(/_/g," "); }
  function bytePositions(source) { const positions=new Map([[0,0]]); let bytes=0,units=0; for(const char of source){ const point=char.codePointAt(0); bytes+=point<128?1:point<2048?2:point<65536?3:4; units+=char.length; positions.set(bytes,units); } return positions; }

  function mountReadingReader(root, options) {
    options=options||{};
    let bundle=options.document||{sources:[],statements:[],rules:[]};
    let loader=options.loader||null,generation=0,navigationSerial=0;
    let operationStatus="",operationError=false;
    let bookQuery="",bookOpen=null,bookIndex=null,bookSerial=0,bookPage=0,bookSearch,bookResults,bookStatus;
    let allOccurrencesLoaded=!loader;
    let locale=options.locale||bundle.language||"en";
    let state={source:null,statement:null,symbol:null,fact:null,wd:null,focusLine:null};
    let history=[];
    let sources,statements,statementsBySource,facts,symbols,rules,occurrences,usedRules,evidenceNodes,inferences,wellDefinedness;
    let codePane,detailPane,rulebook,ruleGrid,ruleSearch,usedOnly,paging;
    let rulePage=0,activeRule=null;
    let rulebookState={query:"",usedOnly:true,open:false,category:"all"};
    let destroyed=false;
    function lang(){return locale.startsWith("zh")?"zh":"en";}
    function t(key){return copy[lang()][key]||key;}
    function index(){
      sources=new Map(array(bundle.sources).map(value=>[value.id,value]));
      statements=new Map(array(bundle.statements).map(value=>[value.id,value]));
      statementsBySource=new Map();for(const value of statements.values()){if(!statementsBySource.has(value.source_id))statementsBySource.set(value.source_id,[]);statementsBySource.get(value.source_id).push(value);}
      facts=new Map(array(bundle.facts).map(value=>[value.id,value]));
      symbols=new Map(array(bundle.symbols).map(value=>[value.id,value]));
      rules=new Map(array(bundle.rules).map(value=>[value.id,value]));
      evidenceNodes=new Map(array(bundle.evidence_nodes).map(value=>[value.id,value.node]));
      inferences=new Map(array(bundle.inferences).map(value=>[value.id,value]));
      wellDefinedness=new Map(array(bundle.well_definedness).map(value=>[value.id,value]));
      occurrences=array(bundle.occurrences);
      if(!statements.size)rulebookState.usedOnly=false;
      usedRules=new Map();
      for(const statement of statements.values())for(const id of statementRules(statement)){if(!usedRules.has(id))usedRules.set(id,new Set());usedRules.get(id).add(statement.id);}
      if(!sources.has(state.source))state.source=sources.has(bundle.entry_source_id)?bundle.entry_source_id:sources.keys().next().value||null;
      if(!statements.has(state.statement)){state.statement=initialStatement(state.source)?.id||null;state.focusLine=statements.get(state.statement)?.line||null;}
    }
    function initialStatement(sourceId){const entries=statementsBySource.get(sourceId)||[];return entries.find(value=>value.status==="accepted"&&array(value.cited_fact_ids).length)||entries[0];}
    function walkEvidence(value,callback,seen=new Set()){
      const pending=[value];
      while(pending.length){const node=pending.pop();if(!node||typeof node!=="object")continue;callback(node);
        if(node.kind==="evidence_reference"){const key="evidence:"+node.evidence_id;if(!seen.has(key)){seen.add(key);pending.push(evidenceNodes.get(node.evidence_id));}}
        else if(node.kind==="statement_reference"){const key="statement:"+node.statement_id;if(!seen.has(key)){seen.add(key);pending.push(statements.get(node.statement_id)?.evidence);}}
        else pending.push(...(Array.isArray(node)?node:Object.values(node)).slice().reverse());
      }
    }
    function statementRules(statement){if(Array.isArray(statement.rule_ids))return new Set(statement.rule_ids);const applied=new Set();walkEvidence(statement.evidence,node=>{if(node.rule_id)applied.add(node.rule_id);});return applied;}
    function resolveEvidence(value){const seen=new Set();while(value?.kind==="evidence_reference"){if(seen.has(value.evidence_id))return {kind:"unavailable"};seen.add(value.evidence_id);value=evidenceNodes.get(value.evidence_id);}return value||{kind:"unavailable"};}
    function factLocation(fact){const producer=statements.get(fact?.producer_statement_id);if(factInferences(fact?.id).length&&producer)return {sourceId:producer.source_id,line:producer.line};return {sourceId:fact?.source_id||producer?.source_id,line:fact?.line||producer?.line};}
    async function navigate(next, remember=true){
      const serial=++navigationSerial,epoch=generation;
      const sourceId=statements.get(next.statement)?.source_id||next.source||state.source;
      try{
        if(loader&&sources.has(sourceId)&&typeof sources.get(sourceId).content!=="string"){
          operationStatus=t("loading");operationError=false;render();
          const chunk=await loader.loadSource(sourceId);
          if(destroyed||epoch!==generation)return false;
          mergeReadingChunk(bundle,chunk);index();
          if(serial!==navigationSerial)return false;
        }
        if(loader&&next.symbol&&!allOccurrencesLoaded){
          operationStatus=t("loadingIndex");operationError=false;render();
          const part=await loader.loadOccurrences();
          if(destroyed||epoch!==generation)return false;
          mergeReadingChunk(bundle,part);allOccurrencesLoaded=true;index();
          if(serial!==navigationSerial)return false;
        }
      }catch(error){if(epoch===generation&&serial===navigationSerial&&!destroyed){operationStatus=t("loadFailed")+": "+error.message;operationError=true;render();}return false;}
      if(destroyed||epoch!==generation||serial!==navigationSerial)return false;
      operationStatus="";operationError=false;
      if(remember)history.push({...state});
      state={...state,...next};
      if(next.statement){const statement=statements.get(next.statement);if(statement)state.source=statement.source_id;}
      render();
      if(state.focusLine)root.querySelector('[data-line="'+state.focusLine+'"]')?.scrollIntoView({block:"nearest",behavior:"smooth"});
      if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});
      return true;
    }
    function selectStatement(id,line){return navigate({statement:id,symbol:null,fact:null,wd:null,focusLine:line||statements.get(id)?.line});}
    function selectSymbol(id){return navigate({symbol:id,fact:null,wd:null,focusLine:null});}
    function factInferences(id){return array(facts.get(id)?.inference_ids).map(key=>inferences.get(key)).filter(Boolean);}
    function selectFact(id){const fact=facts.get(id);if(!fact)return false;const producer=statements.get(fact.producer_statement_id),location=factLocation(fact);return navigate({statement:producer?.id||null,source:producer?.source_id||(sources.has(location.sourceId)?location.sourceId:state.source),symbol:null,fact:id,wd:null,focusLine:producer?(location.sourceId===producer.source_id?location.line:producer.line):(sources.has(location.sourceId)?location.line:null)});}
    function selectWellDefinedness(id){const record=wellDefinedness.get(id);if(!record)return false;const producer=statements.get(record.producer_statement_id);return navigate({statement:producer?.id||null,source:producer?.source_id||state.source,symbol:null,fact:null,wd:id,focusLine:producer?.line||null});}
    function wdCitations(record){const cited=new Set(factCitations({evidence:record?.evidence}));if(facts.has(record?.source_fact_id))cited.add(record.source_fact_id);return [...cited];}
    function factCitations(fact){const cited=new Set(),inferred=factInferences(fact?.id),outputs=new Set(inferred.flatMap(value=>array(value.fact_ids)));for(const inference of inferred)cited.add(inference.source_fact_id);for(const evidence of inferred.length?inferred.map(value=>value.evidence):[fact?.evidence])walkEvidence(evidence,node=>{if(node.kind==="fact_reference"&&node.fact_id!==fact?.id&&!outputs.has(node.fact_id)&&facts.has(node.fact_id))cited.add(node.fact_id);});return [...cited];}
    function ruleTitle(id){const rule=rules.get(id);return rule?.labels?.[lang()]?.name||rule?.name||humanize(rule?.variant||id.split(".").pop());}
    function ruleMessage(id){const rule=rules.get(id);return rule?.labels?.[lang()]?.message||rule?.message||"";}
    function label(role){return roles[role]?.[lang()==="zh"?1:0]||humanize(role);}
    function badge(content,failed){return element("span","lr-badge"+(failed?" lr-badge-failed":""),content);}
    function section(title){const node=element("div","lr-section-label",title);detailPane.append(node);}

    function render(){
      if(destroyed)return;
      root.replaceChildren();root.classList.add("lr-root");
      const toolbar=element("div","lr-toolbar");
      const titleBlock=element("div","lr-title-block");titleBlock.append(element("p","lr-kicker",t("title")));const heading=element("div","lr-book-heading");titleBlock.append(heading);toolbar.append(titleBlock);
      const actions=element("div","lr-toolbar-actions");
      const back=button("←","lr-button",async()=>{const previous=history.pop();if(previous&&!await navigate(previous,false))history.push(previous);});back.disabled=!history.length;back.setAttribute("aria-label",t("back"));actions.append(back);
      const source=sources.get(state.source);
      heading.append(element("h1","lr-book-title",source?.path||"Litex Reading"));
      if(sources.size)heading.append(badge(bundle.run_result==="success"?t("verified"):t("failed"),bundle.run_result!=="success"));
      const trustCount=array(bundle.trust_summary?.user_assumptions).length+array(bundle.trust_summary?.axioms).length;if(trustCount)heading.append(element("span","lr-origin-note",t("trust")+" · "+trustCount));
      const download=button(t("download"),"lr-button lr-download",async()=>{
        const epoch=generation,snapshot=bundle.bundle_id;download.disabled=true;
        try{
          let complete=bundle;
          if(loader?.downloadUrl){const response=await fetch(loader.downloadUrl);if(!response.ok)throw new Error("Reading HTTP "+response.status);complete=await response.json();if(complete.kind!=="reading"||(snapshot&&complete.bundle_id!==snapshot))throw new Error(t("changedBuild"));}
          if(destroyed||epoch!==generation)return;
          const url=URL.createObjectURL(new Blob([JSON.stringify(complete,null,2)],{type:"application/json"}));
          const link=element("a");link.href=url;link.download="book.reading.json";document.body.append(link);link.click();link.remove();setTimeout(()=>URL.revokeObjectURL(url),1000);
        }catch(error){if(!destroyed&&epoch===generation){operationStatus=t("loadFailed")+": "+error.message;operationError=true;render();}}
        finally{download.disabled=false;}
      });if(sources.size)actions.append(download);toolbar.append(actions);root.append(toolbar);
      if(operationStatus){const notice=element("p",operationError?"lr-diagnostics":"lr-loading",operationStatus);notice.setAttribute("role",operationError?"alert":"status");root.append(notice);}
      if(array(bundle.diagnostics).length){const diagnostics=element("div","lr-diagnostics");diagnostics.setAttribute("role","status");for(const diagnostic of bundle.diagnostics)diagnostics.append(element("div",null,diagnostic.message||diagnostic.kind));root.append(diagnostics);}
      if(!sources.size){const empty=element("section","lr-empty");const mark=element("div","lr-empty-mark","∀");mark.setAttribute("aria-hidden","true");empty.append(mark,element("h2",null,t("empty")),element("p",null,t("emptyHint")));root.append(empty);renderRulebook();return;}
      const guide=element("div","lr-reading-guide");guide.append(element("p",null,t("hint")));const legend=element("div","lr-legend");legend.append(element("span",null,t("selectedLegend")),element("span",null,t("premiseLegend")),element("span",null,t("occurrenceLegend")),element("span",null,t("inferred")));guide.append(legend);root.append(guide);
      renderBookNavigation();
      const layout=element("div","lr-layout");
      const sourcePane=element("section","lr-source-pane");const header=element("div","lr-pane-header");header.append(element("span",null,t("source")));
      const select=element("select");select.setAttribute("aria-label",t("source"));for(const item of sources.values()){const option=element("option",null,item.path);option.value=item.id;option.selected=item.id===state.source;select.append(option);}select.addEventListener("change",()=>{const statement=initialStatement(select.value);navigate({source:select.value,statement:statement?.id||null,symbol:null,fact:null,wd:null,focusLine:null});});header.append(select);
      codePane=element("div","lr-code");sourcePane.append(header,codePane);
      const details=element("section","lr-details");const inspectorHeader=element("div","lr-pane-header lr-inspector-header");inspectorHeader.append(element("span","lr-inspector-title",state.symbol?t("concepts"):t("why")));details.append(inspectorHeader);
      const steps=statementsBySource.get(state.source)||[];const current=steps.findIndex(value=>value.id===state.statement);const stepNav=element("nav","lr-step-nav");stepNav.setAttribute("aria-label",t("source"));
      const previous=button("← "+t("previousStep"),"lr-button",()=>selectStatement(steps[current-1].id));previous.disabled=current<=0;
      const next=button(t("nextStep")+" →","lr-button",()=>selectStatement(steps[current+1].id));next.disabled=current<0||current>=steps.length-1;stepNav.append(previous,element("span",null,(current+1)+" / "+steps.length),next);details.append(stepNav);
      detailPane=element("div","lr-detail-body");detailPane.setAttribute("aria-live","polite");details.append(detailPane);layout.append(sourcePane,details);root.append(layout);
      renderCode();if(state.symbol)renderSymbol();else if(state.wd)renderWellDefinedness();else if(state.fact)renderFact();else if(!state.statement&&state.focusLine)renderSourceLine();else renderStatement();
      renderRulebook();
    }

    function owningStatement(sourceId,line,offset){
      const candidates=(statementsBySource.get(sourceId)||[]).filter(value=>value.line<=line&&value.end_byte>value.start_byte&&value.end_byte>offset);
      if(!candidates.length)return null;
      const width=candidates.reduce((size,value)=>Math.min(size,value.end_byte-value.start_byte),Infinity);
      const narrow=candidates.filter(value=>value.end_byte-value.start_byte===width);
      const selected=narrow.find(value=>value.id===state.statement);if(selected)return selected;
      const ancestors=new Set();let current=statements.get(state.statement);while(current&&!ancestors.has(current.id)){ancestors.add(current.id);current=statements.get(current.parent_statement_id);}
      return narrow.find(value=>ancestors.has(value.parent_statement_id))||narrow.find(value=>value.id===(value.source_statement_id||value.id))||narrow[0];
    }

    function selectBookLine(entry){
      const candidates=[...facts.values()].filter(fact=>fact.is_primary&&fact.role&&fact.source_id===entry.source_id&&fact.line===entry.line&&fact.producer_statement_id===entry.statement_id&&!factInferences(fact.id).length);
      if(candidates.length===1)return selectFact(candidates[0].id);
      return navigate({source:entry.source_id,statement:entry.statement_id||null,symbol:null,fact:null,wd:null,focusLine:entry.line});
    }

    function renderBookNavigation(){
      const details=element("details","lr-book-nav");details.open=bookOpen??sources.size>1;details.addEventListener("toggle",()=>{bookOpen=details.open;});details.append(element("summary",null,t("book")+" · "+sources.size));
      const chapters=element("nav","lr-chapters");chapters.setAttribute("aria-label",t("chapters"));
      const dependencies=element("details","lr-book-dependencies");dependencies.open=sources.get(state.source)?.role==="dependency";const dependencyLinks=element("div","lr-chapters");let dependencyCount=0;
      for(const source of sources.values()){
        const link=button(source.path,"lr-chapter"+(source.id===state.source?" lr-active-chapter":""),()=>{const first=initialStatement(source.id);return navigate({source:source.id,statement:first?.id||null,symbol:null,fact:null,wd:null,focusLine:first?.line||1});});
        if(source.id===state.source)link.setAttribute("aria-current","page");
        if(source.role==="dependency"){dependencyLinks.append(link);dependencyCount++;}else chapters.append(link);
      }
      details.append(chapters);if(dependencyCount){dependencies.append(element("summary",null,t("dependencies")+" · "+dependencyCount),dependencyLinks);details.append(dependencies);}
      const tools=element("div","lr-book-search");bookSearch=element("input");bookSearch.type="search";bookSearch.placeholder=t("bookSearch");bookSearch.setAttribute("aria-label",t("bookSearch"));bookSearch.value=bookQuery;bookStatus=element("output","lr-empty-note");bookStatus.setAttribute("aria-live","polite");tools.append(bookSearch,bookStatus);bookResults=element("div","lr-book-results");details.append(tools,bookResults);root.append(details);
      bookSearch.addEventListener("input",()=>{bookQuery=bookSearch.value;bookPage=0;renderBookResults();});if(bookQuery)renderBookResults();
    }

    async function renderBookResults(){
      const serial=++bookSerial,epoch=generation,query=bookQuery.trim().toLowerCase();
      bookResults.replaceChildren();bookStatus.textContent="";if(!query)return;
      if(bookIndex===null){
        bookStatus.textContent=t("loadingIndex");
        try{
          if(loader){const part=await loader.loadSearch();if(destroyed||epoch!==generation)return;bookIndex=array(part.entries);}
          else{
            bookIndex=[];const encoder=new TextEncoder();
            for(const source of sources.values()){let offset=0;for(const [index,line] of String(source.content||"").split("\n").entries()){if(line.trim()){const owner=owningStatement(source.id,index+1,offset);bookIndex.push({source_id:source.id,line:index+1,text:line,statement_id:owner?.source_statement_id||owner?.id||null});}offset+=encoder.encode(line).length+1;}}
          }
        }catch(error){if(epoch===generation&&serial===bookSerial){bookStatus.textContent=t("loadFailed")+": "+error.message;}return;}
      }
      if(destroyed||epoch!==generation||serial!==bookSerial)return;
      const matches=bookIndex.filter(entry=>[entry.text,sources.get(entry.source_id)?.path].join(" ").toLowerCase().includes(query));
      const pageSize=24,pages=Math.max(1,Math.ceil(matches.length/pageSize));bookPage=Math.min(bookPage,pages-1);bookStatus.textContent=matches.length?matches.length+" · "+(bookPage+1)+" / "+pages:t("noMatches");
      for(const entry of matches.slice(bookPage*pageSize,(bookPage+1)*pageSize)){
        const result=button("","lr-fact-link lr-book-result",()=>selectBookLine(entry));result.append(element("code",null,entry.text),element("small",null,(sources.get(entry.source_id)?.path||"")+" · "+t("sourceLine")+" "+entry.line));bookResults.append(result);
      }
      if(pages>1){const paging=element("div","lr-rule-paging"),previous=button("← "+t("previous"),"lr-button",()=>{bookPage--;renderBookResults();}),next=button(t("next")+" →","lr-button",()=>{bookPage++;renderBookResults();});previous.disabled=bookPage===0;next.disabled=bookPage+1>=pages;paging.append(previous,next);bookResults.append(paging);}
    }

    function renderSourceLine(){
      const source=sources.get(state.source);detailPane.append(element("p","lr-eyebrow",t("sourceText")+" · "+t("sourceLine")+" "+state.focusLine),element("h2","lr-statement",String(source?.content||"").split("\n")[state.focusLine-1]||""),element("p","lr-empty-note",t("noStatement")));
    }

    function renderCode(){
      const source=sources.get(state.source);if(!source)return;
      const content=source.content||"";const offsets=bytePositions(content);
      const sourceStatements=statementsBySource.get(source.id)||[];
      const selected=statements.get(state.statement);
      const citations=state.wd?wdCitations(wellDefinedness.get(state.wd)):state.fact?factCitations(facts.get(state.fact)):array(selected?.cited_fact_ids);
      const premiseLines=new Set(citations.map(id=>factLocation(facts.get(id))).filter(value=>value.sourceId===source.id).map(value=>value.line));
      const literalFacts=new Map();for(const fact of facts.values())if(fact.is_primary&&fact.source_id===source.id&&fact.role&&!factInferences(fact.id).length){if(!literalFacts.has(fact.line))literalFacts.set(fact.line,[]);literalFacts.get(fact.line).push(fact);}
      function selectLine(owning,line){if(!owning)return;const candidates=(literalFacts.get(line)||[]).filter(fact=>fact.producer_statement_id===owning.id);if(candidates.length===1)selectFact(candidates[0].id);else selectStatement(owning.id,line);}
      const mentions=occurrences.filter(value=>value.source_id===source.id).map(value=>({...value,start:offsets.get(value.start_byte),end:offsets.get(value.end_byte)})).filter(value=>value.start!==undefined&&value.end!==undefined).sort((a,b)=>a.start-b.start);
      const inferredAfter=new Map();
      for(const statement of sourceStatements){
        const end=offsets.get(statement.end_byte);if(end===undefined)continue;
        const line=content.slice(0,end).trimEnd().split("\n").length;
        for(const id of array(statement.inferred_fact_ids))if(facts.has(id)&&factInferences(id).length){if(!inferredAfter.has(line))inferredAfter.set(line,[]);inferredAfter.get(line).push(id);}
      }
      let lineStart=0,lineByteStart=0;const encoder=new TextEncoder();
      const lines=content.split("\n");
      for(let i=0;i<lines.length;i++){
        const lineNumber=i+1,line=lines[i],lineEnd=lineStart+line.length;
        const owning=owningStatement(source.id,lineNumber,lineByteStart);
        const row=element("div","lr-code-row");row.dataset.line=String(lineNumber);if(owning)row.dataset.statement=owning.id;
        if(state.focusLine?lineNumber===state.focusLine:owning?.id===state.statement)row.classList.add("lr-selected");else if(premiseLines.has(lineNumber))row.classList.add("lr-premise");
        const number=button(String(lineNumber),"lr-line-number",()=>selectLine(owning,lineNumber));number.disabled=!owning;number.setAttribute("aria-label",t("sourceLine")+" "+lineNumber);row.append(number);
        const code=element("code");let cursor=lineStart;
        for(const occurrence of mentions.filter(value=>value.start>=lineStart&&value.end<=lineEnd)){
          if(occurrence.start<cursor)continue;
          code.append(document.createTextNode(content.slice(cursor,occurrence.start)));
          const token=button(content.slice(occurrence.start,occurrence.end),"lr-token",event=>{event.stopPropagation();selectSymbol(occurrence.symbol_id);});token.dataset.symbol=occurrence.symbol_id;token.title=symbols.get(occurrence.symbol_id)?.name||"";
          if(occurrence.symbol_id===state.symbol)token.classList.add("lr-symbol-selected");code.append(token);cursor=occurrence.end;
        }
        code.append(document.createTextNode(content.slice(cursor,lineEnd)||(!line?" ":"")));row.append(code);code.addEventListener("click",()=>selectLine(owning,lineNumber));codePane.append(row);lineStart=lineEnd+1;lineByteStart+=encoder.encode(line).length+1;
        for(const id of new Set(inferredAfter.get(lineNumber)||[])){
          const fact=facts.get(id);const inferred=button("","lr-inferred-row",()=>selectFact(id));inferred.dataset.fact=id;inferred.setAttribute("aria-label",t("inferred")+" "+fact.text);
          const arrow=element("span","lr-inferred-arrow","→");arrow.setAttribute("aria-hidden","true");inferred.append(arrow,element("code",null,fact.text));
          if(fact.scope_id&&!String(fact.scope_id).startsWith("file:"))inferred.append(element("small",null,t("local")));
          if(id===state.fact)inferred.classList.add("lr-inferred-selected");else if(citations.includes(id))inferred.classList.add("lr-inferred-premise");
          codePane.append(inferred);
        }
      }
      const selectedRow=codePane.querySelector(".lr-inferred-selected")||codePane.querySelector(".lr-selected");if(selectedRow){const rowBounds=selectedRow.getBoundingClientRect(),paneBounds=codePane.getBoundingClientRect();if(rowBounds.bottom>paneBounds.bottom||rowBounds.top<paneBounds.top)codePane.scrollTop+=rowBounds.top-paneBounds.top-codePane.clientHeight/3;}
    }

    function factButton(id){
      const fact=facts.get(id);const producer=statements.get(fact?.producer_statement_id);
      const inferred=factInferences(id).length>0;
      const node=button("","lr-fact-link"+(inferred?" lr-inferred-link":""),()=>selectFact(id));
      node.append(element("code",null,(inferred?"→ ":"")+(fact?.text||id)));
      const location=factLocation(fact);const source=sources.get(location.sourceId);node.append(element("small",null,[source?.path,location.line?t("sourceLine")+" "+location.line:null].filter(Boolean).join(" · ")));
      if(fact?.scope_id&&!String(fact.scope_id).startsWith("file:"))node.append(element("small",null,t("local")));
      if(!fact)node.disabled=true;
      return node;
    }

    function renderStatement(){
      const statement=statements.get(state.statement);if(!statement){detailPane.append(element("p","lr-empty-note",t("emptyHint")));return;}
      const parent=statements.get(statement.parent_statement_id);if(parent)detailPane.append(button(t("outerProof")+" · "+t("sourceLine")+" "+parent.line,"lr-chip",()=>selectStatement(parent.id)));
      const instances=[...statements.values()].filter(value=>(value.source_statement_id||value.id)===(statement.source_statement_id||statement.id));if(instances.length>1){const contexts=element("div","lr-contexts");instances.forEach((instance,index)=>{const pick=button(t("context")+" "+(index+1),"lr-chip",()=>selectStatement(instance.id));pick.setAttribute("aria-pressed",String(instance.id===statement.id));contexts.append(pick);});detailPane.append(contexts);}
      const citations=array(statement.cited_fact_ids);if(citations.length){section(t("premise"));citations.forEach(id=>detailPane.append(factButton(id)));detailPane.append(element("div","lr-therefore",t("therefore")));}
      const conclusion=element("div","lr-conclusion");const conclusionHeader=element("div","lr-conclusion-header");const verdict=statement.status==="accepted"?t("accepted"):statement.status==="rejected"?t("rejected"):t("notExported");conclusionHeader.append(element("p","lr-eyebrow",t("sourceLine")+" "+statement.line),badge(verdict,statement.status!=="accepted"));conclusion.append(conclusionHeader,element("h2","lr-statement",statement.text));
      const meta=element("div","lr-detail-meta");meta.append(element("span","lr-meta-note",t("engine")+" Litex "+(bundle.engine?.version||"")));conclusion.append(meta);detailPane.append(conclusion);
      renderOrigin(statement);
      if(statement.status==="rejected")detailPane.append(element("p","lr-empty-note",t("notFalse")));
      if(statement.coverage?.evidence!=="complete"||statement.coverage?.occurrences!=="complete")detailPane.append(element("p","lr-empty-note",t("unavailable")));
      if(statement.coverage?.source_mapping==="partial")detailPane.append(element("p","lr-empty-note",t("sourceMappingGap")));
      if(statement.coverage?.well_definedness==="partial")detailPane.append(element("p","lr-empty-note",t("wdGap")));
      if(array(statement.inferred_fact_ids).length){section(t("inferredFacts"));for(const id of statement.inferred_fact_ids)detailPane.append(factButton(id));}
      if(!citations.length)detailPane.append(element("p","lr-empty-note",t("noPremise")));
      section(t("rules"));const applied=statementRules(statement);if(!applied.size)detailPane.append(element("p","lr-empty-note",t("noRules")));for(const id of applied)detailPane.append(button(ruleTitle(id),"lr-chip",()=>showRule(id)));
      const concepts=new Set(occurrences.filter(value=>value.statement_id===(statement.source_statement_id||statement.id)).map(value=>value.symbol_id));if(concepts.size){section(t("concepts"));for(const id of concepts)detailPane.append(button(symbols.get(id)?.name||id,"lr-chip lr-concept-chip",()=>selectSymbol(id)));}
      const declarations=array(statement.declaration_dependencies);if(declarations.length){section(t("declarations"));for(const id of declarations){const target=statements.get(id);if(target)detailPane.append(button(target.text+" · "+t("sourceLine")+" "+target.line,"lr-fact-link",()=>selectStatement(id)));}}
      section(t("proof"));detailPane.append(evidenceNode(statement.evidence,t("proof")));
      const raw=element("details","lr-raw");raw.append(element("summary",null,t("raw")));raw.addEventListener("toggle",()=>{if(raw.open&&raw.childElementCount===1)raw.append(element("pre",null,JSON.stringify(statement,null,2)));});detailPane.append(raw);
    }

    function renderFact(){
      const fact=facts.get(state.fact);if(!fact)return;
      if(factInferences(fact.id).length){renderInferredFact();return;}
      const producer=statements.get(fact.producer_statement_id);
      const citations=factCitations(fact);if(citations.length){section(fact.role==="hypothesis"?t("formation"):t("premise"));citations.forEach(id=>detailPane.append(factButton(id)));}
      const conclusion=element("div","lr-conclusion");const role=fact.role==="verified"?"verifiedFact":fact.role||"fact";conclusion.append(element("p","lr-eyebrow",t(role)),element("h2","lr-statement",fact.text));
      if(fact.scope_id&&!String(fact.scope_id).startsWith("file:"))conclusion.append(element("p","lr-empty-note",t("local")));detailPane.append(conclusion);
      if(fact.role==="hypothesis"||fact.role==="declaration")detailPane.append(element("p","lr-empty-note",t(fact.role+"Hint")));
      if(producer)renderOrigin(producer);
      const applied=new Set();walkEvidence(fact.evidence,node=>{if(node.rule_id)applied.add(node.rule_id);});if(applied.size){section(t("rules"));for(const id of applied)detailPane.append(button(ruleTitle(id),"lr-chip",()=>showRule(id)));}
      const concepts=new Set(occurrences.filter(value=>value.statement_id===(producer?.source_statement_id||producer?.id)).map(value=>value.symbol_id));if(concepts.size){section(t("concepts"));for(const id of concepts)detailPane.append(button(symbols.get(id)?.name||id,"lr-chip lr-concept-chip",()=>selectSymbol(id)));}
      if(fact.evidence){section(fact.role==="hypothesis"?t("formation"):t("proof"));detailPane.append(evidenceNode(fact.evidence,t("proof")));}
      else if(!["hypothesis","declaration"].includes(fact.role))detailPane.append(element("p","lr-empty-note",t("factProofGap")));
      if(producer)detailPane.append(button(t("producer")+" · "+t("sourceLine")+" "+producer.line,"lr-chip",()=>selectStatement(producer.id)));
      else detailPane.append(element("p","lr-empty-note",t("factSourceGap")));
    }

    function renderInferredFact(){
      const fact=facts.get(state.fact);const producer=statements.get(fact.producer_statement_id);
      if(producer)renderOrigin(producer);
      for(const inference of factInferences(state.fact)){
        section(t("inferredFrom"));detailPane.append(factButton(inference.source_fact_id));
        detailPane.append(element("div","lr-therefore",t("therefore")));
        const conclusion=element("div","lr-conclusion lr-inferred-conclusion");conclusion.append(element("p","lr-eyebrow",t("inferred")),element("h2","lr-statement",fact.text));
        if(fact.scope_id&&!String(fact.scope_id).startsWith("file:"))conclusion.append(element("p","lr-empty-note",t("local")));detailPane.append(conclusion);
        section(t("rules"));for(const id of array(inference.rule_ids))detailPane.append(button(ruleTitle(id),"lr-chip",()=>showRule(id)));
        section(t("proof"));detailPane.append(evidenceNode(inference.evidence,t("proof")));
      }
      if(producer)detailPane.append(button(t("producer")+" · "+t("sourceLine")+" "+producer.line,"lr-chip",()=>selectStatement(producer.id)));
    }

    function renderWellDefinedness(){
      const record=wellDefinedness.get(state.wd);if(!record)return;
      const producer=statements.get(record.producer_statement_id);
      const card=element("div","lr-conclusion");card.append(element("p","lr-eyebrow",t("wellDefined")),element("h2","lr-statement",record.object));detailPane.append(card,element("p","lr-empty-note",t("registrationHint")));
      if(record.scope_id&&!String(record.scope_id).startsWith("file:"))detailPane.append(element("p","lr-empty-note",t("local")));
      if(producer)renderOrigin(producer);
      const citations=wdCitations(record);if(citations.length){section(t("formation"));citations.forEach(id=>detailPane.append(factButton(id)));}
      if(record.evidence){section(t("formation"));detailPane.append(evidenceNode(record.evidence,t("formation")));}
      else detailPane.append(element("p","lr-empty-note",t("registrationProof")));
      if(producer)detailPane.append(button(t("producer")+" · "+t("sourceLine")+" "+producer.line,"lr-chip",()=>selectStatement(producer.id)));
      else detailPane.append(element("p","lr-empty-note",t("wdGap")));
      if(record.registration){section(t("registration"));detailPane.append(evidenceNode(record.registration,t("registration")));}
    }

    function renderOrigin(statement){
      if(statement.origin&&statement.origin!=="checked")detailPane.append(element("p","lr-origin-note",t(statement.origin)));
      const dependencies=array(statement.trust_dependencies);if(dependencies.length&&statement.origin==="checked"){const notice=element("div","lr-origin-note",t("trustUsed"));for(const id of dependencies){const target=statements.get(id);if(target)notice.append(button(t(target.origin)+" · "+t("sourceLine")+" "+target.line,"lr-chip",()=>selectStatement(id)));}detailPane.append(notice);}
    }

    function renderSymbol(){
      const symbol=symbols.get(state.symbol);const mentions=occurrences.filter(value=>value.symbol_id===state.symbol);const definitions=mentions.filter(value=>value.definition);
      detailPane.append(element("p","lr-eyebrow",t("concepts")),element("h2","lr-statement",symbol?.name||state.symbol));
      section(t("definition"));if(!definitions.length)detailPane.append(element("p","lr-empty-note",t("noDefinition")));for(const occurrence of definitions)occurrenceButton(occurrence);
      section(t("references")+" · "+mentions.length);for(const occurrence of mentions)occurrenceButton(occurrence);
    }
    function occurrenceButton(occurrence){const statement=statements.get(occurrence.statement_id);if(!statement)return;const node=button("","lr-fact-link",()=>selectStatement(statement.id,statement.line));node.append(element("code",null,statement.text),element("small",null,(sources.get(occurrence.source_id)?.path||"")+" · "+t("sourceLine")+" "+statement.line));detailPane.append(node);}

    function evidenceNode(value,title){
      value=resolveEvidence(value);
      if(value===null||value===undefined)return element("span","lr-empty-note","—");
      if(typeof value!=="object")return element("span","lr-evidence-subject",String(value));
      if(value.kind==="fact_reference")return factButton(value.fact_id);
      if(value.kind==="fact_identity")return element("span","lr-empty-note",value.fact_id);
      if(value.kind==="well_definedness_reference"||value.kind==="well_definedness_identity"){const record=wellDefinedness.get(value.id);const link=button(t("wellDefined")+" · "+(record?.object||value.id),"lr-fact-link",()=>selectWellDefinedness(value.id));link.disabled=!record;return link;}
      if(value.kind==="statement_reference"){const target=statements.get(value.statement_id);return button((target?.text||value.statement_id)+" · "+t("sourceLine")+" "+(target?.line||""),"lr-fact-link",()=>selectStatement(value.statement_id));}
      if(value.kind==="declaration_reference"){const target=statements.get(value.statement_id);const link=button((target?.text||t("definition"))+" · "+t("sourceLine")+" "+value.line,"lr-fact-link",()=>selectStatement(value.statement_id));link.disabled=!target;return link;}
      if(value.kind==="symbol_reference")return button(value.name||value.symbol_id,"lr-chip lr-concept-chip",()=>selectSymbol(value.symbol_id));
      if(value.kind==="scope")return element("span","lr-empty-note",t("local"));
      if(value.kind==="unavailable")return element("span","lr-empty-note",t("unavailable"));
      const details=element("details","lr-evidence");
      const route=routeNames[value.variant]?.[lang()==="zh"?1:0];
      const summary=element("summary",null,value.rule_id?ruleTitle(value.rule_id):(route||title||humanize(value.variant)||t("proof")));details.append(summary);
      details.addEventListener("toggle",()=>{
        if(!details.open||details.childElementCount>1)return;
        const body=element("div");if(value.text)body.append(element("code","lr-evidence-subject",value.text));
        if(value.rule_id){body.append(button(t("rulebook")+" ↗","lr-chip",()=>showRule(value.rule_id)));const message=ruleMessage(value.rule_id);if(message)body.append(element("p","lr-empty-note",message));}
        const entries=Array.isArray(value)?value.map((item,index)=>[String(index+1),item]):Object.entries(value.fields||value).filter(([key])=>!["text","type","variant","rule_id"].includes(key));
        for(const [key,item] of entries){if(item===null||(Array.isArray(item)&&!item.length))continue;body.append(element("div","lr-evidence-label",label(key)),evidenceNode(item,label(key)));}details.append(body);
      });
      return details;
    }

    function renderRulebook(){
      rulebook=element("details","lr-rulebook");rulebook.open=rulebookState.open;rulebook.addEventListener("toggle",()=>{rulebookState.open=rulebook.open;});rulebook.append(element("summary",null,t("rulebook")+" · "+rules.size));
      const tools=element("div","lr-rulebook-tools");ruleSearch=element("input");ruleSearch.type="search";ruleSearch.placeholder=t("search");ruleSearch.setAttribute("aria-label",t("search"));
      ruleSearch.value=rulebookState.query;const usedLabel=element("label");usedOnly=element("input");usedOnly.type="checkbox";usedOnly.checked=rulebookState.usedOnly;usedLabel.append(usedOnly,document.createTextNode(" "+t("usedOnly")));tools.append(ruleSearch,usedLabel);rulebook.append(tools);
      const categories=element("select");categories.setAttribute("aria-label",t("category"));for(const category of ["all",...new Set([...rules.values()].map(rule=>rule.category).filter(Boolean))]){const option=element("option",null,category==="all"?t("allCategories"):t(category));option.value=category;option.selected=category===rulebookState.category;categories.append(option);}tools.insertBefore(categories,usedLabel);categories.addEventListener("change",()=>{rulebookState.category=categories.value;rulePage=0;renderRules();});
      ruleGrid=element("div","lr-rule-grid");paging=element("div","lr-rule-paging");rulebook.append(ruleGrid,paging);root.append(rulebook);
      ruleSearch.addEventListener("input",()=>{rulebookState.query=ruleSearch.value;rulePage=0;renderRules();});usedOnly.addEventListener("change",()=>{rulebookState.usedOnly=usedOnly.checked;rulePage=0;renderRules();});renderRules();
    }
    function renderRules(){
      const query=ruleSearch.value.trim().toLowerCase();const list=[...rules.values()].filter(rule=>(!usedOnly.checked||usedRules.has(rule.id))&&(rulebookState.category==="all"||rule.category===rulebookState.category)&&[rule.id,ruleTitle(rule.id),rule.variant,ruleMessage(rule.id)].join(" ").toLowerCase().includes(query));
      const pageSize=18;const pages=Math.max(1,Math.ceil(list.length/pageSize));rulePage=Math.min(rulePage,pages-1);ruleGrid.replaceChildren();paging.replaceChildren();
      for(const rule of list.slice(rulePage*pageSize,(rulePage+1)*pageSize)){
        const card=element("article","lr-rule-card"+(rule.id===activeRule?" lr-active-rule":""));card.dataset.rule=rule.id;card.append(element("h3",null,ruleTitle(rule.id)),element("p",null,ruleMessage(rule.id)||t("catalogueOnly")));
        for(const id of usedRules.get(rule.id)||[]){const statement=statements.get(id);card.append(button(t("sourceLine")+" "+statement.line,"lr-chip",()=>selectStatement(id)));}ruleGrid.append(card);
      }
      const previous=button("← "+t("previous"),"lr-button",()=>{rulePage--;renderRules();});previous.disabled=rulePage===0;
      const next=button(t("next")+" →","lr-button",()=>{rulePage++;renderRules();});next.disabled=rulePage+1>=pages;paging.append(previous,element("span",null,(rulePage+1)+" / "+pages+" · "+list.length),next);
    }
    function showRule(id){activeRule=id;rulebookState={query:id,usedOnly:false,open:true,category:"all"};rulebook.open=true;ruleSearch.value=id;usedOnly.checked=false;rulebook.querySelector("select").value="all";rulePage=0;renderRules();rulebook.scrollIntoView({block:"nearest",behavior:"smooth"});}

    index();render();
    return {
      update(document){if(document.kind==="reading_manifest")throw new Error("Use LitexReading.open for a manifest");generation++;navigationSerial++;bookSerial++;loader=null;allOccurrencesLoaded=true;bookIndex=null;bookQuery="";bookOpen=null;operationStatus="";bundle=document;history=[];state={source:null,statement:null,symbol:null,fact:null,wd:null,focusLine:null};activeRule=null;rulePage=0;rulebookState={query:"",usedOnly:true,open:false,category:"all"};index();render();if(options.onNavigate)options.onNavigate({...state},{bundle_id:bundle.bundle_id||null});},
      setLanguage(value){locale=value;render();},
      selectStatement(id){return statements.has(id)?selectStatement(id):false;},
      selectFact(id){return facts.has(id)?selectFact(id):false;},
      selectWellDefinedness(id){return wellDefinedness.has(id)?selectWellDefinedness(id):false;},
      getSelection(){return {...state};},
      getBundleId(){return bundle.bundle_id||null;},
      destroy(){destroyed=true;generation++;navigationSerial++;bookSerial++;root.replaceChildren();}
    };
  }
  function mergeReadingChunk(bundle,part){
    for(const key of ["sources","statements","facts","inferences","well_definedness","evidence_nodes","occurrences"]){
      if(!Array.isArray(part[key]))continue;
      const identity=value=>key==="occurrences"?[value.source_id,value.start_byte,value.end_byte,value.symbol_id,value.statement_id,value.definition].join("|"):value.id;
      const records=new Map(array(bundle[key]).map(value=>[identity(value),value]));
      for(const value of part[key]){const id=identity(value),existing=records.get(id);if(key==="evidence_nodes"&&existing&&JSON.stringify(existing.node)!==JSON.stringify(value.node))throw new Error("Conflicting reading evidence: "+id);records.set(id,{...existing,...value});}
      bundle[key]=[...records.values()];
    }
  }

  async function openReadingReader(root,source,options){
    options=options||{};
    const base=new URL(typeof source==="string"?source:options.baseUrl||location.href,document.baseURI);
    const fetchJSON=async(url,cache="default")=>{const response=await fetch(url,{cache});if(!response.ok)throw new Error("Reading HTTP "+response.status);return response.json();};
    const manifest=typeof source==="string"?await fetchJSON(base.href,"no-store"):source;
    if(manifest?.kind==="reading")return mountReadingReader(root,{...options,document:manifest});
    if(manifest?.kind!=="reading_manifest"||!["1","2"].includes(manifest.schema_version)||typeof manifest.manifest_id!=="string")throw new Error("Unsupported reading manifest");
    const localURL=path=>{const url=new URL(path,base);if(url.origin!==base.origin)throw new Error("Reading parts must share the manifest origin");return url.href;};
    const part=async(path,kind)=>{const value=await fetchJSON(localURL(path));if(value.kind!==kind||value.manifest_id!==manifest.manifest_id)throw new Error((options.locale||manifest.language||"").startsWith("zh")?copy.zh.changedBuild:copy.en.changedBuild);return value;};
    const sources=new Map(array(manifest.sources).map(value=>[value.id,value]));
    const pending=new Map();let occurrencePromise,searchPromise;
    const loader={
      loadSource(id){if(!pending.has(id)){const source=sources.get(id);if(!source)throw new Error("Unknown reading source");pending.set(id,part(source.chunk_url,"reading_chunk").then(value=>{if(value.source_id!==id||value.sources?.length!==1||value.sources[0].id!==id)throw new Error("Mismatched reading source");return value;}).catch(error=>{pending.delete(id);throw error;}));}return pending.get(id);},
      loadOccurrences(){return occurrencePromise||(occurrencePromise=part(manifest.occurrences_url,"reading_occurrences").catch(error=>{occurrencePromise=null;throw error;}));},
      loadSearch(){return searchPromise||(searchPromise=part(manifest.search_url,"reading_search").catch(error=>{searchPromise=null;throw error;}));},
      downloadUrl:localURL(manifest.full_document_url)
    };
    const bundle={...manifest,kind:"reading",sources:array(manifest.sources).map(value=>({...value})),evidence_nodes:[],occurrences:[]};
    const first=sources.has(manifest.entry_source_id)?manifest.entry_source_id:sources.keys().next().value;
    if(first){root.replaceChildren(element("p","lr-loading",(options.locale||manifest.language||"").startsWith("zh")?copy.zh.loading:copy.en.loading));mergeReadingChunk(bundle,await loader.loadSource(first));}
    return mountReadingReader(root,{...options,document:bundle,loader});
  }

  global.LitexReading=Object.freeze({mount:mountReadingReader,open:openReadingReader,schemaVersion:"2",supportedSchemaVersions:Object.freeze(["1","2"])});
})(window);
