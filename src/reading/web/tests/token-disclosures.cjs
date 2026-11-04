'use strict';
// Adjacent named-language help uses real records and unmodified public events.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const {spawnSync}=require('node:child_process'),{createDOM}=require('./dom.cjs');
const binary=path.resolve(process.argv[2]||'target/release/litex');
const file=path.resolve('examples/reading/lessons/en/sqrt-two.lit');
const run=spawnSync(binary,['-reading','-json','-strict','-lang','en','-f',file],{encoding:'utf8',maxBuffer:32*1024*1024});
assert.equal(run.status,0,run.stderr);const bundle=JSON.parse(run.stdout);assert.equal(bundle.run_result,'success');
const code=fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8');
function mount(locale,editable,data=bundle){
  const before=JSON.stringify(data),dom=createDOM(),root=dom.root(),timers=new Map();let now=0,next=0;
  vm.runInContext(code,vm.createContext({...dom,TextEncoder,URL,Map,Set,console,setTimeout(fn,ms){timers.set(++next,{fn,at:now+ms});return next;},clearTimeout(id){timers.delete(id);}}));
  const reader=dom.window.LitexReading.mount(root,{document:data,locale,...(editable?{onCheck:async()=>data}:{})});
  return {...dom,root,reader,
    row(line){return root.querySelector('[data-line="'+line+'"]');},card(){return root.querySelector('.lr-proof-popover');},
    async tick(ms){const end=now+ms;for(;;){const due=[...timers].filter(([,v])=>v.at<=end).sort((a,b)=>a[1].at-b[1].at)[0];if(!due)break;now=due[1].at;timers.delete(due[0]);await due[1].fn();}now=end;},
    async hover(token){if(editable){dom.document.elementFromPoint=()=>token;await root.querySelector('.lr-ide-input').trigger('pointermove',{clientX:100,clientY:80});}else await token.trigger('mouseenter');await this.tick(460);return root.querySelector('.lr-proof-symbol:not([hidden])')||root.querySelector('.lr-token-help');},
    async click(toggle){if(editable){const input=root.querySelector('.lr-ide-input');input.setSelectionRange(4,4);dom.document.elementFromPoint=()=>toggle;const e=await input.trigger('pointerdown',{clientX:100,clientY:80});assert(e.defaultPrevented&&e.stopped);assert.equal(input.selectionStart,4);}else{await dom.document.dispatch('pointerdown',{target:toggle});await toggle.click();}},
    done(){assert.equal(JSON.stringify(data),before,'language disclosures never mutate source, scopes or proof records');reader.destroy();}
  };
}
async function main(){
  let checked=0;
  for(const locale of ['en','zh'])for(const editable of [false,true]){
    const v=mount(locale,editable),selection=JSON.stringify(v.reader.getSelection()),rows=v.root.querySelectorAll('.lr-code-row').length;
    for(const [line,heading] of [[6,'by contra'],[7,'sqrt']]){
      const token=v.row(line).querySelectorAll('[data-syntax]').find(t=>t.textContent===heading);assert(token,heading);
      const anchor=token.parentNode,toggle=anchor.querySelector('.lr-help-toggle');assert(anchor.matches('.lr-help-anchor'));assert.strictEqual(anchor.children[0],token);assert.equal(toggle.dataset.help,heading);assert.equal(toggle.textContent,'▸');
      const tip=await v.hover(token);assert(tip,heading);const expected=tip.textContent;await v.root.trigger('keydown',{key:'Escape'});
      await v.click(toggle);let card=v.card();assert(card);assert.equal(card.querySelector('.lr-proof-body').textContent,expected,'the exact typed/operation-specific hover renderer is reused');
      assert.equal(toggle.textContent,'▾');assert.equal(toggle.getAttribute('aria-expanded'),'true');assert.equal(toggle.getAttribute('aria-controls'),card.id);assert.strictEqual(v.document.activeElement,toggle);assert.equal(JSON.stringify(v.reader.getSelection()),selection);
      assert(!card.querySelector('.lr-proof-evidence'),'a help card is not a proof of the containing statement');
      await v.row(line).trigger('pointerleave');await card.trigger('pointerleave');await v.tick(1000);assert.strictEqual(v.card(),card);
      await v.hover(token);assert.strictEqual(v.card(),card);assert(!v.root.querySelector('.lr-token-help'),'hover cannot cover a clicked help card with a second bubble');
      await v.click(toggle);assert(!v.card());assert.equal(toggle.textContent,'▸');
      await v.click(toggle);await v.root.trigger('keydown',{key:'Escape'});assert(!v.card());assert.strictEqual(v.document.activeElement,toggle);
      await v.click(toggle);await toggle.trigger('keydown',{key:'ArrowRight'});assert(v.card().contains(v.document.activeElement));await v.root.trigger('keydown',{key:'Escape'});assert.strictEqual(v.document.activeElement,toggle);
      await v.click(toggle);await v.card().querySelector('.lr-explanation-close').click();assert(!v.card());assert.strictEqual(v.document.activeElement,toggle);await v.tick(1000);assert(!v.card());
      await v.click(toggle);await v.document.dispatch('pointerdown',{target:v.root});assert(!v.card());assert.equal(toggle.getAttribute('aria-expanded'),'false');checked++;
    }
    const first=v.row(7).querySelector('[data-help="sqrt"]'),other=v.row(15).querySelector('[data-help="sqrt"]');assert(other,'each repeated source occurrence owns its own adjacent button');await v.click(first);await v.click(other);assert.equal(first.textContent,'▸');assert.equal(other.textContent,'▾');assert.equal(v.root.querySelectorAll('.lr-proof-popover').length,1);
    const proof=v.row(15).querySelector('.lr-proof-toggle');await v.click(proof);assert.equal(other.textContent,'▸');assert(v.card().querySelector('.lr-proof-evidence'),'the sentence proof remains independent');
    assert(!v.root.querySelector('.lr-help-toggle[data-help="p"]'));assert(!v.root.querySelector('.lr-help-toggle[data-help="2"]'));assert(!v.root.querySelector('.lr-help-toggle[data-help="("]'));
    assert.equal(v.root.querySelectorAll('.lr-code-row').length,rows);
    if(editable){const input=v.root.querySelector('.lr-ide-input');assert.equal(input.value,fs.readFileSync(file,'utf8'));input.value+=' ';await input.trigger('input');assert.equal(v.root.querySelectorAll('.lr-explanation-toggle,.lr-proof-popover').length,0);}
    v.done();
  }
  const rejectedRun=spawnSync(binary,['-reading','-json','-strict','-lang','en','-f',path.resolve('examples/reading/lessons/en/sqrt-domain.lit')],{encoding:'utf8',maxBuffer:16*1024*1024});
  assert.equal(rejectedRun.status,1);const rejected=JSON.parse(rejectedRun.stdout);assert.equal(rejected.run_result,'failure');
  const failed=mount('en',true,rejected),toggle=failed.root.querySelector('[data-help="sqrt"]');assert(toggle);await failed.click(toggle);assert(failed.card().textContent.includes('x ≥ 0'));assert(!failed.card().querySelector('.lr-proof-evidence'),'operation help never certifies an invalid application');assert(failed.root.querySelector('.lr-rejected'));failed.done();
  console.log(JSON.stringify({passed:true,checked,bilingualEditableReadOnly:true,adjacentNativeButtons:true,originalTokensAndSourceUnchanged:true,exactHelpRenderer:true,keywordAndOperationDistinctFromProof:true,repeatSwitchAndDismiss:true,keyboardFocus:true,caretAndEditInvalidation:true,hoverPreserved:true,failedDomainNotCertified:true,browserGeometry:false}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
