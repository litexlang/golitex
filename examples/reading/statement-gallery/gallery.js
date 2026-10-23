(function () {
  "use strict";
  const catalogue=window.LitexStatementGallery,designs=catalogue.designs;
  const byId=new Map(designs.map(value=>[value.id,value]));
  const primary=designs.filter(value=>!value.fact_form),factForms=designs.filter(value=>value.leaf==="Fact");
  const nav=document.getElementById("type-navigation"),search=document.getElementById("search"),select=document.getElementById("type-select"),code=document.getElementById("example-code"),meaning=document.getElementById("meaning"),dialog=document.getElementById("explanation-dialog"),help=document.getElementById("type-help");
  const groups=["定义","对象","函数","事实","证明","展开","见证","性质","假设与公理","计算"];
  const plans={equivalence:"首行放完整命题及 ⇔；换行缩进后，保留全部参数类型和定义条件。",cases:"输入与输出范围放在前面，条件与对应结果用分段形式一一对齐。",recursion:"函数范围、初始值和递归步骤分别占行，保留递归参数的实际范围。",induction:"基础情形、归纳步骤和最终目标分开排列，区分普通归纳与强归纳的假设。",premises:"将全部前提按顺序保留在上方，再用推导符号连接结论。",contradiction:"依次呈现实际反设、矛盾和最终结论。",flow:"从已有条件到取出的对象及其性质，按依赖顺序竖排。"};
  let current,dialogOpener;
  function el(tag,cls,text){const n=document.createElement(tag);if(cls)n.className=cls;if(text!==undefined)n.textContent=text;return n;}
  function openDialog(title,body){dialogOpener=document.activeElement;document.getElementById("dialog-title").textContent=title;document.getElementById("dialog-body").replaceChildren(...body);if(!dialog.open)dialog.showModal();document.getElementById("close-dialog").focus();}
  document.getElementById("close-dialog").addEventListener("click",()=>dialog.close());
  dialog.addEventListener("click",event=>{if(event.target===dialog){const r=dialog.getBoundingClientRect();if(event.clientX<r.left||event.clientX>r.right||event.clientY<r.top||event.clientY>r.bottom)dialog.close();}});
  dialog.addEventListener("close",()=>{if(dialogOpener?.isConnected)dialogOpener.focus();else help.focus();});
  function navigation(){
    const query=search.value.trim().toLowerCase();nav.replaceChildren();let count=0;
    for(const group of groups){const entries=primary.filter(d=>d.group===group&&[d.title,d.syntax,d.leaf].some(s=>s.toLowerCase().includes(query)));if(!entries.length)continue;const section=el("div","gallery-group"),heading=el("h2",null,group);section.append(heading);
      for(const item of entries){const b=el("button",null);b.type="button";b.dataset.id=item.id;b.setAttribute("aria-current",String(current?.leaf===item.leaf));b.append(el("span",null,item.title),el("small",null,item.syntax));b.addEventListener("click",()=>choose(item.id));section.append(b);count++;}nav.append(section);
    }document.getElementById("no-results").hidden=!!count;
  }
  function choose(id){if(!byId.has(id))id="DefPropStmt";if(location.hash!=="#"+id)history.replaceState(null,"","#"+id);current=byId.get(id);render();}
  function render(){
    const d=current;document.getElementById("selection-title").textContent=d.title;document.getElementById("check-status").textContent=d.trust_count?"例子已接受 · 含假设/公理":"例子检查通过";
    select.value=d.leaf;help.textContent=d.syntax+" ⓘ";help.setAttribute("aria-label","了解 "+d.title);
    document.getElementById("example-download").href="examples/"+d.id+".lit";
    const forms=document.getElementById("fact-forms");forms.replaceChildren();forms.hidden=d.leaf!=="Fact";
    if(d.leaf==="Fact")for(const item of factForms){const b=el("button",null,item.title);b.type="button";b.setAttribute("aria-pressed",String(item.id===d.id));b.addEventListener("click",()=>choose(item.id));forms.append(b);}
    const scope=document.getElementById("scope-label");scope.textContent=d.badge||"";scope.hidden=!d.badge;
    code.replaceChildren();const inferred=new Map();for(const fact of d.inferred){if(!inferred.has(fact.line))inferred.set(fact.line,[]);inferred.get(fact.line).push(fact);}
    for(const [index,line] of d.code.trimEnd().split("\n").entries()){
      const row=el("div","gallery-code-line"),number=index+1;if(number>=d.focus_lines[0]&&number<=d.focus_lines[1])row.classList.add("is-focus");row.dataset.line=number;
      row.append(el("span","line-number",number));const content=el("span",null);content.append(el("code",null,line||" "));
      if(inferred.has(number)){const results=el("span","gallery-inline");results.setAttribute("aria-label","本句实际推导结果");results.append(el("span",null,"→"));for(const fact of inferred.get(number)){const b=el("button",null,fact.text);b.type="button";b.addEventListener("click",()=>openDialog("推导事实",[el("pre",null,fact.text),el("p",null,"这是该例子实际发布的推导结果，可以被后面的语句引用。这里保留原始事实文本，完整数学排版仍是展示稿的设计内容。")]));results.append(b);}content.append(results);}row.append(content);code.append(row);
    }
    const focus=code.querySelector(".is-focus");code.scrollTop=0;if(focus)code.scrollTop=Math.max(0,focus.getBoundingClientRect().top-code.getBoundingClientRect().top-28);
    meaning.replaceChildren();document.querySelector(".gallery-meaning").dataset.layout=d.layout||"formula";
    for(const tex of d.math){const node=el("div","gallery-math");try{window.katex.render(tex,node,{displayMode:true,throwOnError:true,trust:false,strict:"ignore",maxExpand:500,maxSize:50,output:"htmlAndMathml"});}catch(error){node.classList.add("gallery-render-error");node.textContent="公式未能排版："+tex;}meaning.append(node);}
    navigation();
  }
  help.addEventListener("click",()=>openDialog("什么是 "+current.syntax+" 语句？",[el("p",null,current.help),el("p","gallery-dialog-subtitle","对应展示的安排"),el("p",null,plans[current.layout]||"默认只展示这条语句的具体数学内容。完整上下文保留在源码区，语句的语言说明按需打开。" )]));
  for(const group of groups){const optgroup=el("optgroup",null);optgroup.label=group;for(const d of primary.filter(d=>d.group===group)){const option=el("option",null,d.title+" · "+d.syntax);option.value=d.id;optgroup.append(option);}if(optgroup.children.length)select.append(optgroup);}
  select.addEventListener("change",()=>choose(select.value));search.addEventListener("input",navigation);window.addEventListener("hashchange",()=>choose(location.hash.slice(1)));
  document.getElementById("inventory-label").textContent=catalogue.leaf_count+" 种语句 · "+designs.length+" 个例子";
  choose(location.hash.slice(1)||"DefPropStmt");
})();
