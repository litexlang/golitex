#!/usr/bin/env node
// Render the editable SVG source with an optional local Playwright installation.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { chromium } = require("playwright");

(async () => {
  const executablePath = process.env.CHROME_EXECUTABLE;
  const browser = await chromium.launch({ headless: true, ...(executablePath ? { executablePath } : {}) });
  const records = {};
  try {
  for (const suffix of ["", ".zh"]) {
    const svg = fs.readFileSync(path.join(__dirname, `proof-search${suffix}.svg`), "utf8");
    const print = await browser.newPage({ viewport: { width: 1200, height: 824 } });
    await print.setContent(`<html><head><title>Proof as a search | Litex</title><style>@page{size:183mm 125.66mm;margin:0}html,body{margin:0;padding:0;background:white}svg{display:block;width:183mm;height:125.66mm}</style></head><body>${svg}</body></html>`);
    await print.evaluate(() => document.fonts.ready);
    await print.pdf({ path: path.join(__dirname, `proof-search${suffix}.pdf`), preferCSSPageSize: true, printBackground: true, tagged: true });
    await print.close();
    const raster = await browser.newPage({ viewport: { width: 1200, height: 824 }, deviceScaleFactor: 600 * 183 / 25.4 / 1200 });
    await raster.setContent(`<html><head><style>html,body{margin:0;padding:0;background:white}svg{display:block;width:1200px;height:824px}</style></head><body>${svg}</body></html>`);
    await raster.evaluate(() => document.fonts.ready);
    const overflow = await raster.locator("svg").evaluate(svg => [...svg.querySelectorAll("text")].filter(node => {
      const b = node.getBoundingClientRect();
      return b.left < -1 || b.top < -1 || b.right > 1201 || b.bottom > 825;
    }).map(node => node.textContent));
    if (overflow.length) throw new Error(`Text outside figure: ${overflow.join("; ")}`);
    await raster.locator("svg").screenshot({ path: path.join(__dirname, `proof-search${suffix}.png`) });
    await raster.close();
    for (const format of ["svg", "pdf", "png"]) {
      const name = `proof-search${suffix}.${format}`;
      records[name] = crypto.createHash("sha256").update(fs.readFileSync(path.join(__dirname, name))).digest("hex");
    }
    console.log(`Exported SVG text as vector PDF and high-resolution PNG: ${suffix || "en"}`);
  }
  const acceptancePath = path.join(__dirname, "acceptance.json");
  const acceptance = JSON.parse(fs.readFileSync(acceptancePath, "utf8"));
  acceptance.rendered_assets = records;
  fs.writeFileSync(acceptancePath, JSON.stringify(acceptance, null, 2)+"\n");
  } finally {
    await browser.close();
  }
})().catch(error => { console.error(error);process.exitCode = 1; });
