// Deterministic offline DOM/event fixture. This models no CSS/layout engine and
// is not browser or visual acceptance. Tests run the unmodified public reader.
"use strict";
function createDOM(){
class Node {
 constructor(tag='',text=''){this.tagName=tag;this.own=text;this.childNodes=[];this.parentNode=null;this.attrs={};this.dataset={};this.style={};this.handlers={};this.className='';this.hidden=false;this.clientHeight=720;this.clientWidth=1280;this.scrollTop=0;this.scrollLeft=0;}
 get children(){return this.childNodes.filter(n=>n.tagName);}
 get textContent(){return this.own+this.childNodes.map(n=>n.textContent).join('');}
 set textContent(v){this.own=String(v);this.childNodes=[];}
 get innerText(){return this.textContent;}
 get classList(){return {add:(...v)=>{this.className=[...new Set(this.className.split(/\s+/).filter(Boolean).concat(v))].join(' ')},remove:(...v)=>{this.className=this.className.split(/\s+/).filter(x=>!v.includes(x)).join(' ')},contains:v=>this.className.split(/\s+/).includes(v),toggle:(v,on)=>{const set=new Set(this.className.split(/\s+/).filter(Boolean));on??=!set.has(v);on?set.add(v):set.delete(v);this.className=[...set].join(' ');return on}};}
 append(...values){for(let n of values){if(typeof n==='string')n=new Node('',n);if(n.parentNode)n.remove();n.parentNode=this;this.childNodes.push(n);}}
 prepend(...values){const old=this.childNodes.slice();this.childNodes=[];this.append(...values,...old);}
 replaceChildren(...values){for(const n of this.childNodes)n.parentNode=null;this.own='';this.childNodes=[];this.append(...values);}
 setAttribute(k,v){this.attrs[k]=String(v);if(k==='class')this.className=String(v);if(k.startsWith('data-'))this.dataset[k.slice(5).replace(/-([a-z])/g,(_,x)=>x.toUpperCase())]=String(v);}
 getAttribute(k){return k==='class'?this.className:this.attrs[k]??null;}
 removeAttribute(k){delete this.attrs[k];}
 addEventListener(k,fn){(this.handlers[k]??=[]).push(fn);}
 removeEventListener(k,fn){this.handlers[k]=(this.handlers[k]||[]).filter(value=>value!==fn);}
 remove(){if(this.parentNode){this.parentNode.childNodes=this.parentNode.childNodes.filter(n=>n!==this);this.parentNode=null;}}
 contains(n){while(n){if(n===this)return true;n=n.parentNode;}return false;}
 get isConnected(){return document.body.contains(this);}
 matches(s){s=s.trim();const not=/:not\(([^)]+)\)/.exec(s);if(not){if(this.matches(not[1]))return false;s=s.replace(not[0],'');}if(s.split(/(?=[.#\[])/)[0]&&!s.startsWith('.')&&!s.startsWith('[')&&!s.startsWith('#')){const tag=/^[\w-]+/.exec(s)?.[0];if(tag&&this.tagName!==tag)return false;}
  for(const [,c] of s.matchAll(/\.([\w-]+)/g))if(!this.classList.contains(c))return false;
  const id=/#([\w-]+)/.exec(s);if(id&&this.attrs.id!==id[1]&&this.id!==id[1])return false;
  for(const [,key,value] of s.matchAll(/\[([\w-]+)(?:="([^"]*)")?\]/g)){const v=key.startsWith('data-')?this.dataset[key.slice(5).replace(/-([a-z])/g,(_,x)=>x.toUpperCase())]:this.attrs[key];if(v===undefined||value!==undefined&&v!==value)return false;}
  return true;
 }
 querySelectorAll(selector){const results=[],selectors=selector.split(',').map(s=>s.trim().split(/\s+(?![^[]*\])/));const visit=n=>{for(const child of n.children){if(selectors.some(parts=>{if(!child.matches(parts.at(-1)))return false;let p=child.parentNode,i=parts.length-2;while(p&&i>=0){if(p.matches(parts[i]))i--;p=p.parentNode;}return i<0;}))results.push(child);visit(child);}};visit(this);return results;}
 querySelector(s){return this.querySelectorAll(s)[0]||null;}
 closest(s){let n=this;while(n){if(s.split(',').some(p=>n.matches(p)))return n;n=n.parentNode;}return null;}
 getBoundingClientRect(){return this.rect||{left:32,right:1312,top:80,bottom:104,width:1280,height:24};}
 setSelectionRange(start,end){this.selectionStart=start;this.selectionEnd=end;}
 setRangeText(value,start,end){this.value=this.value.slice(0,start)+value+this.value.slice(end);this.setSelectionRange(start+value.length,start+value.length);}
 get childElementCount(){return this.children.length;}
 insertBefore(node,before){if(node.parentNode)node.remove();const index=this.childNodes.indexOf(before);node.parentNode=this;this.childNodes.splice(index<0?this.childNodes.length:index,0,node);}
 showModal(){this.open=true;}
 close(){this.open=false;this.trigger('close');}
 scrollIntoView(){}
 focus(){document.activeElement=this;for(const fn of this.handlers.focus||[])fn({target:this});}
 async trigger(type,init={}){const event={type,target:this,currentTarget:this,defaultPrevented:false,stopped:false,stopPropagation(){this.stopped=true;},preventDefault(){this.defaultPrevented=true;},...init};let node=this;while(node){event.currentTarget=node;for(const fn of [...(node.handlers[type]||[])])await fn(event);if(event.stopped||!['click','pointermove','pointerdown','keydown','keyup','focusin','focusout'].includes(type))break;node=node.parentNode;}return event;}
 async click(init={}){const event=await this.trigger('click',init);if(!event.defaultPrevented&&this.tagName==='summary'&&this.parentNode?.tagName==='details'){this.parentNode.open=!this.parentNode.open;await this.parentNode.trigger('toggle');}return event;}
}

function events(){const listeners=new Map();return {addEventListener(k,fn){if(!listeners.has(k))listeners.set(k,new Set());listeners.get(k).add(fn);},removeEventListener(k,fn){listeners.get(k)?.delete(fn);},async dispatch(type,init={}){const event={type,defaultPrevented:false,preventDefault(){this.defaultPrevented=true;},stopPropagation(){},...init};for(const fn of [...(listeners.get(type)||[])])await fn(event);return event;}};}
const document={createElement:t=>new Node(t),createTextNode:t=>new Node('',t),documentElement:{clientWidth:1440,clientHeight:900},activeElement:null,...events()};
document.body=new Node('body');
document.querySelector=selector=>document.body.querySelector(selector);
document.querySelectorAll=selector=>document.body.querySelectorAll(selector);
document.getElementById=id=>document.body.querySelector('#'+id);
const window={...events()};
return {document,window,Node,root(){const root=new Node('main');document.body.append(root);return root;}};
}
module.exports={createDOM};
