"use strict";
const fs=require("node:fs"),path=require("node:path"),vm=require("node:vm"),assert=require("node:assert/strict");
const {createDOM}=require("./dom.cjs");
const directory=process.argv[2];
if(!directory)throw new Error("Usage: node src/reading/web/tests/lessons.cjs <fixture-directory-created-with--lessons>");
const code=fs.readFileSync(path.join(__dirname,"../reader.js"),"utf8"),catalogue=JSON.parse(fs.readFileSync(path.join(__dirname,"../../../../examples/reading/lessons/catalogue.json"),"utf8"));
const delay=()=>new Promise(resolve=>setTimeout(resolve,480));
function fixture(name){return JSON.parse(fs.readFileSync(path.join(directory,"lesson-"+name+".json"),"utf8"));}
function mount(bundle,locale,onCheck=async()=>bundle){
  const dom=createDOM(),root=dom.root();vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,setTimeout,clearTimeout,console}));
  const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,onCheck});
  const content=bundle.sources[0].content;
  return {...dom,root,reader,content,line(text,last=false){const lines=content.split("\n"),indices=lines.flatMap((line,index)=>line.trim()===text?[index+1]:[]);assert(indices.length,text);return root.querySelector('[data-line="'+(last?indices.at(-1):indices[0])+'"]');},
    async hover(target){const input=root.querySelector(".lr-ide-input");dom.document.elementFromPoint=()=>target;await input.trigger("pointermove",{clientX:100,clientY:80});await delay();}};
}
async function run(){
  const report=[];
  for(const item of catalogue.lessons)for(const locale of ["zh","en"]){
    const bundle=fixture(item.id+"-"+locale),view=mount(bundle,locale);
    assert.equal(bundle.run_result,item.expected);assert.equal(view.root.querySelectorAll(".lr-code-row").length,view.content.split("\n").length);
    assert(view.root.querySelector(".lr-context-explanation").hidden);assert.equal(view.root.querySelectorAll(".lr-json-pane,.lr-json-toggle").length,0);
    assert.equal(view.root.querySelector(".lr-ide-input").value,view.content);
    if(item.id==="sqrt-two"){
      const row=view.line("p^2 = (sqrt(2) * q)^2 = sqrt(2)^2 * q^2 = 2 * q^2"),tokens=row.querySelectorAll(".lr-chain-equality");assert.equal(tokens.length,3);
      await view.hover(tokens[0]);assert(view.root.querySelector(".lr-proof-grounds").textContent.includes("sqrt (2) = (p / q)"));
      const application=view.line("release thm prime_divides_power(p, 2, 2)");
      assert(application.querySelector(".lr-inference-toggle"),"the divisibility prompt points to actual published grey consequences");
      const theorem=application.querySelectorAll('.lr-token').find(node=>node.textContent==='prime_divides_power');assert(theorem);
      await view.hover(theorem);assert(view.root.querySelector('.lr-token-help').textContent.includes(locale==='zh'?'内置定理':'Builtin theorem'),'a retained builtin theorem does not fall back to object help');
      const keyword=application.querySelector('[data-keyword="release thm"]');assert(keyword,'the complete theorem-release keyword is one help target');
      await view.hover(keyword);assert(view.root.querySelector('.lr-token-help').textContent.includes('prime_divides_power(6, 2, 2)'),'the keyword reference contains its concrete instantiation example');
    }
    if(item.id==="syllogism"){
      const row=view.line("$is_mortal(socrates)",true);await view.hover(row.querySelector(".lr-syntax-predicate"));
      const proof=view.root.querySelector(".lr-proof-popover");assert(proof.textContent.includes("person = socrates"));assert.equal(proof.querySelectorAll(".lr-proof-grounds .lr-fact-link").length,2);
    }
    if(item.id==="definitions"){
      const row=view.line("by def $nonnegative(3)"),result=row.querySelector(".lr-inference-toggle");assert(result);await view.hover(result);
      const results=view.root.querySelector(".lr-inference-popover"),disclosure=results.querySelector('details.lr-inferred-facts');assert(disclosure&&!disclosure.open);await disclosure.querySelector('summary').click();assert(disclosure.open);assert(results.textContent.includes("3 ≥ 0"));
      assert(row.querySelector('[data-keyword="by def"]'),"multiword definition keyword remains one help target");
    }
    if(item.id==="sets"){
      const row=view.line("union({1, 2}, {2, 3}) = union({2, 3}, {1, 2})"),token=row.querySelectorAll(".lr-token,[data-syntax]").find(node=>node.textContent==="union");
      assert(token);await view.hover(token);assert(view.root.querySelector(".lr-token-help").textContent.includes(locale==="zh"?"集合运算符":"Set operator"));
    }
    if(item.id==="cantor"){
      const row=view.line("obtain a from exist a S st {diagonal_set = f(a)}"),token=row.querySelectorAll(".lr-token").find(node=>node.textContent==="a");assert(token);
      await view.hover(token);assert(view.root.querySelector(".lr-token-help").textContent.includes("S"));
    }
    if(item.id==="least-squares"){
      const row=[...view.root.querySelectorAll(".lr-code-row")].find(node=>node.querySelectorAll(".lr-chain-equality").length===2&&node.textContent.includes("<=")&&node.textContent.includes("candidate"));
      assert(row,"the mathematical comparison retains its two distinct equality targets");
      assert.deepEqual(row.querySelectorAll(".lr-chain-equality").map(token=>Number(token.dataset.chainStep)),[0,2]);
    }
    if(item.expected==="failure"){
      const marker=view.root.querySelector(".lr-inline-failure");assert(marker);await view.hover(marker);
      const card=view.root.querySelector(".lr-proof-popover");assert(card);
      const obligation={"missing-premise":"is_mortal(socrates)","sqrt-domain":"0 ≤ (-1)","definition-failure":"(-1) ≥ 0"}[item.id];assert(card.textContent.includes(obligation));
      const repaired=fixture(item.id+"-repair-"+locale),target=repaired.sources[0].content;
      const input=view.root.querySelector(".lr-ide-input");input.value=target;await input.trigger("input");assert(view.root.querySelector(".lr-pending"));
      // Use an independent mounted view with the real repaired CLI result. Its
      // host callback checks the submitted bytes before returning that result.
      view.reader.destroy();
      const exercise=mount(bundle,locale,async({changes,sourcePath})=>{assert.equal(changes[sourcePath],target);return repaired;});
      const edit=exercise.root.querySelector(".lr-ide-input");edit.value=target;await edit.trigger("input");
      await exercise.root.querySelector(".lr-check").click();assert(!exercise.root.querySelector(".lr-pending"));assert(!exercise.root.querySelector(".lr-inline-failure"));
      assert.equal(exercise.root.querySelector(".lr-ide-input").value,target);exercise.reader.destroy();
    }else view.reader.destroy();
    report.push({lesson:item.id,locale,expected:item.expected,sourceOnly:true,interaction:true});
  }
  console.log(JSON.stringify({passed:true,lessons:report},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
