'use strict';
// Unmodified app/reader, real CLI rechecks, and an in-memory HTTP transport.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict'),{execFileSync}=require('node:child_process');
const {createDOM}=require('./dom.cjs'),[fixture,binary,output]=process.argv.slice(2);
if(!fixture||!binary||!output)throw new Error('Usage: node latex-host.cjs <native-proof-json> <litex> <task-output>');
const initial=JSON.parse(fs.readFileSync(fixture,'utf8')),scratch=path.resolve(output),executable=path.resolve(binary);
fs.mkdirSync(scratch,{recursive:true});
const dom=createDOM(),{document,window}=dom,requests=[];
const node=(tag,id,text='')=>{const n=document.createElement(tag);n.id=id;n.textContent=text;document.body.append(n);return n;};
node('script','reading-data',JSON.stringify(initial));node('select','language');node('label','language-label');node('div','upload-status');
const input=node('input','source-files');node('input','project-files');const root=node('main','reader');document.body.dataset.live='true';document.referrer='';window.parent=window;
const katex=require('../vendor/katex/katex.min.js');window.katex={render(tex,target,options){katex.renderToString(tex,options);target.textContent=tex;}};
let reader;
const context=vm.createContext({...dom,console,URL,URLSearchParams,TextEncoder,Map,Set,setTimeout,clearTimeout,location:{href:'http://reader.test/',search:'',origin:'http://reader.test'},async fetch(url,settings){
 assert.equal(url,'/api/reading/build');const body=JSON.parse(settings.body);requests.push(body);assert.equal(body.latex,true,'the app retains mathematical layout on recheck/upload');
 const directory=path.join(scratch,String(requests.length));fs.mkdirSync(directory,{recursive:true});
 for(const file of body.files){const destination=path.join(directory,file.path);assert(destination.startsWith(directory+path.sep));fs.mkdirSync(path.dirname(destination),{recursive:true});fs.writeFileSync(destination,file.content);}
 const entry=body.entry?.path||body.files.find(file=>file.path.endsWith('.lit')).path,kind=body.entry?.kind==='project'?'-r':'-f';
 const args=['-reading','-latex','-json','-lang',body.language||'en',kind,path.join(directory,entry)];if(body.strict)args.push('-strict');
 const result=JSON.parse(execFileSync(executable,args,{encoding:'utf8',maxBuffer:64*1024*1024}));assert.equal(result.reading_layout,'latex');assert.equal(result.run_result,'success');
 return {ok:true,async json(){return result;}};
}});
vm.runInContext(fs.readFileSync(path.join(__dirname,'../reader.js'),'utf8'),context);
const publicAPI=window.LitexReading;window.LitexReading={...publicAPI,mount:(target,options)=>(reader=publicAPI.mount(target,options))};
async function run(){
 await vm.runInContext(fs.readFileSync(path.join(__dirname,'../app.js'),'utf8'),context);
 assert(root.querySelector('.lr-manuscript'));await root.querySelector('[data-layout="source"]').click();
 const editor=root.querySelector('.lr-ide-input');editor.value+='\n1=1\n';await editor.trigger('input');await root.querySelector('.lr-check').click();
 assert.equal(requests.length,1);assert.equal(requests[0].strict,true);assert(!root.querySelector('.lr-editor-error'));
 await root.querySelector('[data-layout="latex"]').click();assert(root.querySelector('.lr-manuscript'));
 input.files=[{name:'uploaded.lit',size:4,async text(){return '1=1\n';}}];await input.trigger('change');
 assert.equal(requests.length,2);assert(root.querySelector('.lr-manuscript'));assert.equal(reader.getReadingLayout(),'latex');
 reader.destroy();console.log(JSON.stringify({passed:true,actualAppRecheckRetainsLatex:true,actualFileUploadRetainsLatex:true,strictRecheckPreserved:true}));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
