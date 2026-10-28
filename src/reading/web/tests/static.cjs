"use strict";
const fs=require("node:fs"),path=require("node:path"),vm=require("node:vm"),assert=require("node:assert/strict");
const directory=process.argv[2];
if(!directory)throw new Error("Usage: node src/reading/web/tests/static.cjs <fresh-export-directory>");
const html=fs.readFileSync(path.join(directory,"index.html"),"utf8"),script=html.match(/<script>([\s\S]*?)<\/script>/)?.[1];
assert(script,"native export includes the offline page bootstrap");
for(const protocol of ["file:","http:"]){
  const redirects=[];
  vm.runInNewContext(script,{location:{protocol,search:"?lang=en",hash:"#source-step",replace:url=>redirects.push(url)}});
  assert.deepEqual(redirects,protocol==="file:"?["standalone.html?lang=en#source-step"]:[]);
}
console.log(JSON.stringify({passed:true,offlineQueryAndFragmentPreserved:true,httpPageUnchanged:true},null,2));
