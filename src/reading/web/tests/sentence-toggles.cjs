'use strict';
// Real native bundles and public reader events; browser geometry is checked separately.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {spawnSync}=require('node:child_process'),{createDOM}=require('./dom.cjs');
const binary=path.resolve(process.argv[2]||'target/release/litex');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
const source='have p cart(R, R) = (1, 2)\np(1) + p(2) = 3\n';
function native(content,success=true){
  const run=spawnSync(binary,['-reading','-json','-strict','-lang','en','-e',content],{encoding:'utf8',maxBuffer:16*1024*1024});
  assert(!run.error,run.error?.message);assert.equal(run.status,success?0:1,run.stderr||content);
  const bundle=JSON.parse(run.stdout);assert.equal(bundle.run_result,success?'success':'failure');assert.equal(bundle.sources[0].content,content);return bundle;
}
function mount(bundle,locale,editable){
  const before=JSON.stringify(bundle),dom=createDOM(),root=dom.root(),timers=new Map();let now=0,next=0;
  const setTimeout=(fn,ms)=>{timers.set(++next,{fn,at:now+ms});return next;},clearTimeout=id=>timers.delete(id);
  vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,setTimeout,clearTimeout,console}));
  const reader=dom.window.LitexReading.mount(root,{document:bundle,locale,...(editable?{onCheck:async()=>bundle}:{})});
  return {...dom,root,reader,row(line){return root.querySelector('[data-line="'+line+'"]');},
    card(){return root.querySelector('.lr-proof-popover');},
    async tick(ms){const end=now+ms;for(;;){const due=[...timers].filter(([,v])=>v.at<=end).sort((a,b)=>a[1].at-b[1].at)[0];if(!due)break;now=due[1].at;timers.delete(due[0]);await due[1].fn();}now=end;},
    async clickToggle(toggle){
      if(editable){const input=root.querySelector('.lr-ide-input');input.setSelectionRange(3,3);dom.document.elementFromPoint=()=>toggle;const event=await input.trigger('pointerdown',{clientX:100,clientY:80});assert(event.defaultPrevented&&event.stopped,'an ordinary editor click reaches the button');assert.equal(input.selectionStart,3,'the button does not move the caret');}
      else{await dom.document.dispatch('pointerdown',{target:toggle});await toggle.click();}
    },
    done(){assert.equal(JSON.stringify(bundle),before,'the viewer does not change native records');reader.destroy();}
  };
}
async function run(){
  const bundle=native(source);let checked=0;
  for(const locale of ['zh','en'])for(const editable of [false,true]){
    const v=mount(bundle,locale,editable),row=v.row(2),toggle=row.querySelector('.lr-proof-toggle'),selection=JSON.stringify(v.reader.getSelection());
    assert(toggle);assert.equal(toggle.textContent,'▸');assert.equal(toggle.getAttribute('aria-expanded'),'false');
    assert.equal(row.querySelector('.lr-code-content').children[1],toggle,'the button immediately follows the complete source text');
    assert.equal(v.row(3).querySelector('.lr-proof-toggle'),null,'blank source rows receive no invented explanation');
    await row.trigger('pointermove',{target:toggle});await v.tick(1000);assert(!v.card(),'the triangle itself requires a click');
    const sourceCode=row.querySelector('.lr-source-code');
    if(editable){v.document.elementFromPoint=()=>sourceCode;await v.root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}
    else await row.trigger('pointermove',{target:sourceCode});
    await v.tick(460);const hoverText=v.card().querySelector('.lr-proof-evidence').textContent;await v.root.trigger('keydown',{key:'Escape'});
    await v.clickToggle(toggle);let card=v.card();assert(card);assert(card.querySelector('.lr-numeric-rewrite'),'the actual existing proof renderer is reused');
    assert.strictEqual(v.document.activeElement,toggle,'a forwarded editor click focuses the button so Escape reaches the reader');
    assert.equal(toggle.textContent,'▾');assert.equal(toggle.getAttribute('aria-controls'),card.id);assert.equal(toggle.getAttribute('aria-expanded'),'true');
    assert.equal(JSON.stringify(v.reader.getSelection()),selection,'opening the button does not select an arbitrary produced fact');
    const proofText=card.querySelector('.lr-proof-evidence').textContent;
    assert.equal(proofText,hoverText,'click and hover show the exact same proof contents');
    await row.trigger('pointerleave');await card.trigger('pointerleave');await v.tick(1000);assert.strictEqual(v.card(),card,'a clicked explanation stays open after pointer exit');
    await v.clickToggle(toggle);assert(!v.card(),'a second ordinary click closes the same explanation');assert.equal(toggle.textContent,'▸');assert.equal(toggle.getAttribute('aria-controls'),null);
    await v.clickToggle(toggle);await v.root.trigger('keydown',{key:'Escape'});assert(!v.card());assert.equal(toggle.getAttribute('aria-expanded'),'false');
    await v.clickToggle(toggle);await v.document.dispatch('pointerdown',{target:v.root});assert(!v.card());assert.equal(toggle.textContent,'▸');
    await v.clickToggle(toggle);await v.card().querySelector('.lr-explanation-close').click();assert(!v.card());assert.strictEqual(v.document.activeElement,toggle);
    await v.tick(1000);assert(!v.card(),'restoring button focus does not reopen the explanation');
    await v.clickToggle(toggle);await toggle.trigger('keydown',{key:'ArrowRight'});assert(v.card().contains(v.document.activeElement),'keyboard users can enter the open explanation');
    await v.root.trigger('keydown',{key:'Escape'});assert.strictEqual(v.document.activeElement,toggle);assert(!v.card());
    await v.clickToggle(toggle);const other=v.row(1).querySelector('.lr-proof-toggle');assert(other);await v.clickToggle(other);assert.equal(v.root.querySelectorAll('.lr-proof-popover').length,1);assert.equal(toggle.textContent,'▸');assert.equal(other.textContent,'▾');
    await v.clickToggle(toggle);card=v.card();assert.equal(card.querySelector('.lr-proof-evidence').textContent,proofText);
    const cite=card.querySelector('.lr-numeric-rewrite .lr-fact-link');assert(cite);const id=cite.dataset.fact;await cite.click();assert.equal(v.reader.getSelection().fact,id);
    await v.root.querySelector('.lr-back').click();assert.equal(v.reader.getSelection().focusLine,2);assert(v.root.querySelector('.lr-detail-body .lr-numeric-rewrite'),'Back returns to this exact derivation');
    await v.root.trigger('keydown',{key:'Escape'});await v.row(2).querySelector('.lr-proof-toggle').click();
    if(editable){const input=v.root.querySelector('.lr-ide-input');input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-proof-toggle,.lr-proof-popover').length,0,'editing removes every stale disclosure and proof');assert.equal(v.root.querySelectorAll('.lr-code-row').length,3);}
    v.done();checked++;
  }
  const cases=[
    {content:source.replace('= 3','= 4'),success:false,line:2,kind:'failure'},
    {content:'forall x R:\n    x + 0 = x\n',success:true,line:2,kind:'local'},
    {content:source.replace('= 3','= 1 + 2 = 3'),success:true,line:2,kind:'chain'},
    {content:'prop def_zero(x R):\n    x = 0\nby def:\n    ? $def_zero(0)\n',success:true,line:3,kind:'command'}
  ];
  for(const item of cases){
    const b=native(item.content,item.success),v=mount(b,'en',true),toggle=v.row(item.line).querySelector('.lr-proof-toggle');assert(toggle,item.kind);await v.clickToggle(toggle);assert(v.card(),item.kind);
    if(item.kind==='failure')assert(v.card().textContent.includes('not established')||v.card().textContent.includes('not accepted'));
    if(item.kind==='chain')assert(v.row(2).querySelectorAll('.lr-chain-equality').length>=2,'operator-specific proof targets remain available');
    if(item.kind==='local')assert(v.card().textContent.includes('x'),'local variables retain their actual context');
    v.done();checked++;
  }
  const missing=JSON.parse(JSON.stringify(bundle));missing.statements=[];missing.facts=[];missing.inferences=[];
  const v=mount(missing,'en',false);assert.equal(v.root.querySelectorAll('.lr-proof-toggle').length,0,'source text alone never supplies a proof button');v.done();
  console.log(JSON.stringify({passed:true,checked,bilingualEditableReadOnly:true,sameProofRenderer:true,ordinaryEditorClick:true,persistentAndToggle:true,closeEscapeOutsideAndFocus:true,exactCitationAndBack:true,sourceEditInvalidation:true,localFailureChainAndCommand:true,nativeUnchanged:true,browserGeometry:false}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
