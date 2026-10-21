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
    let locale=options.locale||bundle.language||"en";
    let state={source:null,statement:null,symbol:null,focusLine:null};
    let history=[];
    let sources,statements,facts,symbols,rules,occurrences,usedRules;
    let codePane,detailPane,rulebook,ruleGrid,ruleSearch,usedOnly,paging;
    let rulePage=0,activeRule=null;
    let rulebookState={query:"",usedOnly:true,open:false,category:"all"};
    let destroyed=false;
    function lang(){return locale.startsWith("zh")?"zh":"en";}
    function t(key){return copy[lang()][key]||key;}
    function index(){
      sources=new Map(array(bundle.sources).map(value=>[value.id,value]));
      statements=new Map(array(bundle.statements).map(value=>[value.id,value]));
      facts=new Map(array(bundle.facts).map(value=>[value.id,value]));
      symbols=new Map(array(bundle.symbols).map(value=>[value.id,value]));
      rules=new Map(array(bundle.rules).map(value=>[value.id,value]));
      occurrences=array(bundle.occurrences);
      if(!statements.size)rulebookState.usedOnly=false;
      usedRules=new Map();
      for(const statement of statements.values())walkEvidence(statement.evidence,node=>{if(node.rule_id){if(!usedRules.has(node.rule_id))usedRules.set(node.rule_id,new Set());usedRules.get(node.rule_id).add(statement.id);}});
      if(!sources.has(state.source))state.source=sources.has(bundle.entry_source_id)?bundle.entry_source_id:sources.keys().next().value||null;
      if(!statements.has(state.statement))state.statement=initialStatement(state.source)?.id||null;
    }
    function initialStatement(sourceId){const entries=array(bundle.statements).filter(value=>value.source_id===sourceId);return entries.find(value=>value.status==="accepted"&&array(value.cited_fact_ids).length)||entries[0];}
    function walkEvidence(value,callback,seen=new Set()){
      if(!value||typeof value!=="object")return;
      callback(value);
      if(value.kind==="statement_reference"){
        if(!seen.has(value.statement_id)){seen.add(value.statement_id);walkEvidence(statements.get(value.statement_id)?.evidence,callback,seen);}
      }else if(Array.isArray(value))value.forEach(item=>walkEvidence(item,callback,seen));
      else Object.values(value).forEach(item=>walkEvidence(item,callback,seen));
    }
    function factLocation(fact){const producer=statements.get(fact?.producer_statement_id);return {sourceId:fact?.source_id||producer?.source_id,line:fact?.line||producer?.line};}
    function navigate(next, remember=true){
      if(remember)history.push({...state});
      state={...state,...next};
      if(next.statement){const statement=statements.get(next.statement);if(statement)state.source=statement.source_id;}
      render();
      if(state.focusLine)root.querySelector('[data-line="'+state.focusLine+'"]')?.scrollIntoView({block:"nearest",behavior:"smooth"});
      if(options.onNavigate)options.onNavigate({...state});
    }
    function selectStatement(id,line){navigate({statement:id,symbol:null,focusLine:line||statements.get(id)?.line});}
    function selectSymbol(id){navigate({symbol:id,focusLine:null});}
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
      const back=button("←","lr-button",()=>{const previous=history.pop();if(previous)navigate(previous,false);});back.disabled=!history.length;back.setAttribute("aria-label",t("back"));actions.append(back);
      const source=sources.get(state.source);
      heading.append(element("h1","lr-book-title",source?.path||"Litex Reading"));
      if(sources.size)heading.append(badge(bundle.run_result==="success"?t("verified"):t("failed"),bundle.run_result!=="success"));
      const trustCount=array(bundle.trust_summary?.user_assumptions).length+array(bundle.trust_summary?.axioms).length;if(trustCount)heading.append(element("span","lr-origin-note",t("trust")+" · "+trustCount));
      const download=button(t("download"),"lr-button lr-download",()=>{
        const url=URL.createObjectURL(new Blob([JSON.stringify(bundle,null,2)],{type:"application/json"}));
        const link=element("a");link.href=url;link.download="book.reading.json";link.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
      });if(sources.size)actions.append(download);toolbar.append(actions);root.append(toolbar);
      if(array(bundle.diagnostics).length){const diagnostics=element("div","lr-diagnostics");diagnostics.setAttribute("role","status");for(const diagnostic of bundle.diagnostics)diagnostics.append(element("div",null,diagnostic.message||diagnostic.kind));root.append(diagnostics);}
      if(!sources.size){const empty=element("section","lr-empty");const mark=element("div","lr-empty-mark","∀");mark.setAttribute("aria-hidden","true");empty.append(mark,element("h2",null,t("empty")),element("p",null,t("emptyHint")));root.append(empty);renderRulebook();return;}
      const guide=element("div","lr-reading-guide");guide.append(element("p",null,t("hint")));const legend=element("div","lr-legend");legend.append(element("span",null,t("selectedLegend")),element("span",null,t("premiseLegend")),element("span",null,t("occurrenceLegend")));guide.append(legend);root.append(guide);
      const layout=element("div","lr-layout");
      const sourcePane=element("section","lr-source-pane");const header=element("div","lr-pane-header");header.append(element("span",null,t("source")));
      const select=element("select");select.setAttribute("aria-label",t("source"));for(const item of sources.values()){const option=element("option",null,item.path);option.value=item.id;option.selected=item.id===state.source;select.append(option);}select.addEventListener("change",()=>{const statement=initialStatement(select.value);navigate({source:select.value,statement:statement?.id||null,symbol:null,focusLine:null});});header.append(select);
      codePane=element("div","lr-code");sourcePane.append(header,codePane);
      const details=element("section","lr-details");const inspectorHeader=element("div","lr-pane-header lr-inspector-header");inspectorHeader.append(element("span","lr-inspector-title",state.symbol?t("concepts"):t("why")));details.append(inspectorHeader);
      const steps=array(bundle.statements).filter(value=>value.source_id===state.source);const current=steps.findIndex(value=>value.id===state.statement);const stepNav=element("nav","lr-step-nav");stepNav.setAttribute("aria-label",t("source"));
      const previous=button("← "+t("previousStep"),"lr-button",()=>selectStatement(steps[current-1].id));previous.disabled=current<=0;
      const next=button(t("nextStep")+" →","lr-button",()=>selectStatement(steps[current+1].id));next.disabled=current<0||current>=steps.length-1;stepNav.append(previous,element("span",null,(current+1)+" / "+steps.length),next);details.append(stepNav);
      detailPane=element("div","lr-detail-body");detailPane.setAttribute("aria-live","polite");details.append(detailPane);layout.append(sourcePane,details);root.append(layout);
      renderCode();if(state.symbol)renderSymbol();else renderStatement();
      renderRulebook();
    }

    function renderCode(){
      const source=sources.get(state.source);if(!source)return;
      const content=source.content||"";const offsets=bytePositions(content);
      const sourceStatements=array(bundle.statements).filter(value=>value.source_id===source.id);
      const selected=statements.get(state.statement);
      const premiseLines=new Set(array(selected?.cited_fact_ids).map(id=>factLocation(facts.get(id))).filter(value=>value.sourceId===source.id).map(value=>value.line));
      const mentions=occurrences.filter(value=>value.source_id===source.id).map(value=>({...value,start:offsets.get(value.start_byte),end:offsets.get(value.end_byte)})).filter(value=>value.start!==undefined&&value.end!==undefined).sort((a,b)=>a.start-b.start);
      let lineStart=0;
      const lines=content.split("\n");
      for(let i=0;i<lines.length;i++){
        const lineNumber=i+1,line=lines[i],lineEnd=lineStart+line.length;
        const owning=sourceStatements.filter(value=>value.line<=lineNumber&&(offsets.get(value.end_byte)??-1)>=lineStart).at(-1);
        const row=element("div","lr-code-row");row.dataset.line=String(lineNumber);if(owning)row.dataset.statement=owning.id;
        if(owning?.id===state.statement)row.classList.add("lr-selected");else if(premiseLines.has(lineNumber))row.classList.add("lr-premise");
        const number=button(String(lineNumber),"lr-line-number",()=>{if(owning)selectStatement(owning.id,lineNumber);});number.disabled=!owning;number.setAttribute("aria-label",t("sourceLine")+" "+lineNumber);row.append(number);
        const code=element("code");let cursor=lineStart;
        for(const occurrence of mentions.filter(value=>value.start>=lineStart&&value.end<=lineEnd)){
          if(occurrence.start<cursor)continue;
          code.append(document.createTextNode(content.slice(cursor,occurrence.start)));
          const token=button(content.slice(occurrence.start,occurrence.end),"lr-token",event=>{event.stopPropagation();selectSymbol(occurrence.symbol_id);});token.dataset.symbol=occurrence.symbol_id;token.title=symbols.get(occurrence.symbol_id)?.name||"";
          if(occurrence.symbol_id===state.symbol)token.classList.add("lr-symbol-selected");code.append(token);cursor=occurrence.end;
        }
        code.append(document.createTextNode(content.slice(cursor,lineEnd)||(!line?" ":"")));row.append(code);code.addEventListener("click",()=>{if(owning)selectStatement(owning.id,lineNumber);});codePane.append(row);lineStart=lineEnd+1;
      }
      const selectedRow=codePane.querySelector(".lr-selected");if(selectedRow){const rowBounds=selectedRow.getBoundingClientRect(),paneBounds=codePane.getBoundingClientRect();if(rowBounds.bottom>paneBounds.bottom||rowBounds.top<paneBounds.top)codePane.scrollTop+=rowBounds.top-paneBounds.top-codePane.clientHeight/3;}
    }

    function factButton(id){
      const fact=facts.get(id);const producer=statements.get(fact?.producer_statement_id);
      const node=button("","lr-fact-link",()=>{if(producer)selectStatement(producer.id,fact.line||producer.line);});
      node.append(element("code",null,fact?.text||id));
      const location=factLocation(fact);const source=sources.get(location.sourceId);node.append(element("small",null,[source?.path,location.line?t("sourceLine")+" "+location.line:null].filter(Boolean).join(" · ")));
      if(fact?.scope_id&&!String(fact.scope_id).startsWith("file:"))node.append(element("small",null,t("local")));
      if(!producer)node.disabled=true;
      return node;
    }

    function renderStatement(){
      const statement=statements.get(state.statement);if(!statement){detailPane.append(element("p","lr-empty-note",t("emptyHint")));return;}
      const parent=statements.get(statement.parent_statement_id);if(parent)detailPane.append(button(t("outerProof")+" · "+t("sourceLine")+" "+parent.line,"lr-chip",()=>selectStatement(parent.id)));
      const instances=[...statements.values()].filter(value=>(value.source_statement_id||value.id)===(statement.source_statement_id||statement.id));if(instances.length>1){const contexts=element("div","lr-contexts");instances.forEach((instance,index)=>{const pick=button(t("context")+" "+(index+1),"lr-chip",()=>selectStatement(instance.id));pick.setAttribute("aria-pressed",String(instance.id===statement.id));contexts.append(pick);});detailPane.append(contexts);}
      const citations=array(statement.cited_fact_ids);if(citations.length){section(t("premise"));citations.forEach(id=>detailPane.append(factButton(id)));detailPane.append(element("div","lr-therefore",t("therefore")));}
      const conclusion=element("div","lr-conclusion");const conclusionHeader=element("div","lr-conclusion-header");const verdict=statement.status==="accepted"?t("accepted"):statement.status==="rejected"?t("rejected"):t("notExported");conclusionHeader.append(element("p","lr-eyebrow",t("sourceLine")+" "+statement.line),badge(verdict,statement.status!=="accepted"));conclusion.append(conclusionHeader,element("h2","lr-statement",statement.text));
      const meta=element("div","lr-detail-meta");meta.append(element("span","lr-meta-note",t("engine")+" Litex "+(bundle.engine?.version||"")));conclusion.append(meta);detailPane.append(conclusion);
      if(statement.origin&&statement.origin!=="checked")detailPane.append(element("p","lr-origin-note",t(statement.origin)));
      const trustDependencies=array(statement.trust_dependencies);if(trustDependencies.length&&statement.origin==="checked"){const notice=element("div","lr-origin-note",t("trustUsed"));for(const id of trustDependencies){const target=statements.get(id);if(target)notice.append(button(t(target.origin)+" · "+t("sourceLine")+" "+target.line,"lr-chip",()=>selectStatement(id)));}detailPane.append(notice);}
      if(statement.status==="rejected")detailPane.append(element("p","lr-empty-note",t("notFalse")));
      if(statement.coverage?.evidence!=="complete"||statement.coverage?.occurrences!=="complete")detailPane.append(element("p","lr-empty-note",t("unavailable")));
      if(statement.coverage?.source_mapping==="partial")detailPane.append(element("p","lr-empty-note",t("sourceMappingGap")));
      if(!citations.length)detailPane.append(element("p","lr-empty-note",t("noPremise")));
      section(t("rules"));const applied=new Set();walkEvidence(statement.evidence,node=>{if(node.rule_id)applied.add(node.rule_id);});if(!applied.size)detailPane.append(element("p","lr-empty-note",t("noRules")));for(const id of applied)detailPane.append(button(ruleTitle(id),"lr-chip",()=>showRule(id)));
      const concepts=new Set(occurrences.filter(value=>value.statement_id===(statement.source_statement_id||statement.id)).map(value=>value.symbol_id));if(concepts.size){section(t("concepts"));for(const id of concepts)detailPane.append(button(symbols.get(id)?.name||id,"lr-chip lr-concept-chip",()=>selectSymbol(id)));}
      const declarations=array(statement.declaration_dependencies);if(declarations.length){section(t("declarations"));for(const id of declarations){const target=statements.get(id);if(target)detailPane.append(button(target.text+" · "+t("sourceLine")+" "+target.line,"lr-fact-link",()=>selectStatement(id)));}}
      section(t("proof"));detailPane.append(evidenceNode(statement.evidence,t("proof")));
      const raw=element("details","lr-raw");raw.append(element("summary",null,t("raw")));raw.addEventListener("toggle",()=>{if(raw.open&&raw.childElementCount===1)raw.append(element("pre",null,JSON.stringify(statement,null,2)));});detailPane.append(raw);
    }

    function renderSymbol(){
      const symbol=symbols.get(state.symbol);const mentions=occurrences.filter(value=>value.symbol_id===state.symbol);const definitions=mentions.filter(value=>value.definition);
      detailPane.append(element("p","lr-eyebrow",t("concepts")),element("h2","lr-statement",symbol?.name||state.symbol));
      section(t("definition"));if(!definitions.length)detailPane.append(element("p","lr-empty-note",t("noDefinition")));for(const occurrence of definitions)occurrenceButton(occurrence);
      section(t("references")+" · "+mentions.length);for(const occurrence of mentions)occurrenceButton(occurrence);
    }
    function occurrenceButton(occurrence){const statement=statements.get(occurrence.statement_id);if(!statement)return;const node=button("","lr-fact-link",()=>selectStatement(statement.id,statement.line));node.append(element("code",null,statement.text),element("small",null,(sources.get(occurrence.source_id)?.path||"")+" · "+t("sourceLine")+" "+statement.line));detailPane.append(node);}

    function evidenceNode(value,title){
      if(value===null||value===undefined)return element("span","lr-empty-note","—");
      if(typeof value!=="object")return element("span","lr-evidence-subject",String(value));
      if(value.kind==="fact_reference")return factButton(value.fact_id);
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
      update(document){bundle=document;history=[];state={source:null,statement:null,symbol:null,focusLine:null};activeRule=null;rulePage=0;rulebookState={query:"",usedOnly:true,open:false,category:"all"};index();render();},
      setLanguage(value){locale=value;render();},
      selectStatement(id){if(statements.has(id))selectStatement(id);},
      getSelection(){return {...state};},
      destroy(){destroyed=true;root.replaceChildren();}
    };
  }
  global.LitexReading=Object.freeze({mount:mountReadingReader,schemaVersion:"1"});
})(window);
