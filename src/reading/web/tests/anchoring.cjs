"use strict";
// Source anchoring with explicit DOM rectangles. This is not visual acceptance.
const fs=require("node:fs"),path=require("node:path"),vm=require("node:vm"),assert=require("node:assert/strict");
const {createDOM}=require("./dom.cjs");
const directory=process.argv[2];if(!directory)throw new Error("Usage: node anchoring.cjs <fixture-directory>");
const code=fs.readFileSync(path.join(__dirname,"../reader.js"),"utf8"),delay=()=>new Promise(resolve=>setTimeout(resolve,480));
const rect=(left,top,width,height)=>({left,top,right:left+width,bottom:top+height,width,height});
function mount(name){
  const dom=createDOM(),root=dom.root(),bundle=JSON.parse(fs.readFileSync(path.join(directory,name+".json"),"utf8"));
  vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,setTimeout,clearTimeout,console}));
  const reader=dom.window.LitexReading.mount(root,{document:bundle,locale:"en",onCheck:async()=>bundle});
  return {...dom,root,reader};
}
async function run(){
  const pinned=mount("sqrt-two");await pinned.root.querySelector('.lr-code-row[data-line="7"] .lr-chain-equality').click();
  const exact=pinned.root.querySelector('.lr-equality-selected'),panel=pinned.root.querySelector('.lr-context-explanation');assert(exact&&!panel.hidden);
  pinned.root.querySelector('.lr-ide').rect=rect(20,100,1000,500);exact.rect=rect(500,200,10,24);panel.rect=rect(0,0,320,160);
  await pinned.window.dispatch('resize');assert.equal(panel.style.left,'500px','a pinned equality stays at that exact equals sign');
  exact.rect=rect(500,650,10,24);await pinned.window.dispatch('scroll');assert(panel.hidden,'an explanation closes when its source scrolls out of the editor');
  assert.equal(pinned.reader.getSelection().explanationOpen,false);pinned.reader.destroy();

  const help=mount('lesson-definitions-en'),keyword=help.root.querySelector('[data-keyword="prop"]');assert(keyword);
  help.root.querySelector('.lr-ide').rect=rect(20,100,1000,500);keyword.rect=rect(200,200,32,24);await keyword.trigger('mouseenter');assert(help.root.querySelector('.lr-token-help'));
  keyword.rect=rect(200,650,32,24);await help.window.dispatch('scroll');assert(!help.root.querySelector('.lr-token-help'),'keyword help closes at the editor clipping boundary');help.reader.destroy();

  const proof=mount('sqrt-two'),equal=proof.root.querySelector('.lr-chain-equality');
  proof.root.querySelector('.lr-ide').rect=rect(20,100,1000,500);equal.rect=rect(200,200,10,24);await equal.trigger('mouseenter');await delay();assert(proof.root.querySelector('.lr-proof-popover'));
  equal.rect=rect(1100,200,10,24);await proof.window.dispatch('scroll');assert(!proof.root.querySelector('.lr-proof-popover'),'proof help closes when its exact source is horizontally clipped');proof.reader.destroy();

  const inferred=mount('definition'),owner=inferred.root.querySelector('.lr-inference-toggle');assert(owner);
  inferred.root.querySelector('.lr-ide').rect=rect(20,100,1000,500);owner.rect=rect(200,200,160,24);await owner.click();assert(inferred.root.querySelector('.lr-inference-popover'));
  owner.rect=rect(1100,200,160,24);await inferred.window.dispatch('scroll');assert(!inferred.root.querySelector('.lr-inference-popover'));assert.equal(owner.getAttribute('aria-expanded'),'false');inferred.reader.destroy();
  console.log(JSON.stringify({passed:true,pinnedEqualityUsesExactOperator:true,editorClippingDismissesAllSourceCards:true,scope:'offline DOM rectangles; real browser layout remains separate'},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
