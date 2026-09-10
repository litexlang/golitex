import { FileBlob, PresentationFile } from '@oai/artifact-tool';
const p=await PresentationFile.importPptx(await FileBlob.load('scripts/Litex_BP_2026-08_v25_副本.pptx'));
console.log((await p.inspect({kind:'slide,textbox,shape,table,notes,layout',maxChars:30000})).ndjson);
