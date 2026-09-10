import { FileBlob, PresentationFile } from '@oai/artifact-tool';
const p=await PresentationFile.importPptx(await FileBlob.load('scripts/Litex_BP_2026-08_v25_副本.pptx'));
for (let i=0;i<p.slides.items.length;i++) { const s=p.slides.items[i]; console.log('SLIDE',i+1); for(const sh of s.shapes.items){ if(sh.text) { let t=''; try{t=sh.text.text??sh.text.toString()}catch{} if(t.trim()) console.log(JSON.stringify(t)); } } }
