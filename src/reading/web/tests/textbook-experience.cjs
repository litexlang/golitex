'use strict';

const assert = require('node:assert/strict');
const { spawnSync } = require('node:child_process');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const katex = require('../vendor/katex/katex.min.js');
const { createDOM } = require('./dom.cjs');

const binary = path.resolve(process.argv[2] || 'target/release/litex');
const reader = fs.readFileSync(path.join(__dirname, '../reader.js'), 'utf8');
const squareRoot = fs.readFileSync(path.join(__dirname, '../../../../examples/reading/homepage/04-sqrt-two-irrational.lit'), 'utf8');

function compile(source, latex, status = 0) {
  const result = spawnSync(binary, [
    '-reading', ...(latex ? ['-latex'] : []), '-json', '-strict', '-lang', 'zh', '-e', source
  ], { encoding: 'utf8', maxBuffer: 128 * 1024 * 1024 });
  assert.equal(result.status, status, result.stderr || result.stdout?.slice(-800));
  return JSON.parse(result.stdout);
}

function mount(bundle, store = new Map(), editable = false) {
  const dom = createDOM(), root = dom.root();
  dom.window.localStorage = {
    getItem: key => store.get(key),
    setItem: (key, value) => store.set(key, value),
    removeItem: key => store.delete(key)
  };
  dom.window.katex = { render(tex, target, options) {
    const rendered = katex.renderToString(tex, options);
    target.textContent = tex.replace(/\\htmlData\{lr-symbol=[^}]+\}/g, '');
    for (const match of rendered.matchAll(/ data-lr-symbol="([^"]+)"/g)) {
      const marker = dom.document.createElement('span');
      marker.setAttribute('data-lr-symbol', match[1]);
      target.append(marker);
    }
  }};
  vm.runInContext(reader, vm.createContext({ ...dom, URL, TextEncoder, console, setTimeout, clearTimeout }));
  const controller = dom.window.LitexReading.mount(root, {
    document: bundle,
    experience: 'textbook',
    ...(editable ? { onCheck: async ({ changes }) => compile(Object.values(changes)[0], bundle.reading_layout === 'latex') } : {})
  });
  return { root, controller, window: dom.window };
}

function nativeLatex(bundle) {
  return bundle.sources[0].latex_blocks.map(block => block.content).join('');
}

async function run() {
  const math = compile(squareRoot, true);
  const plain = compile(squareRoot, false);
  for (const key of ['facts', 'statements', 'scopes', 'evidence_nodes', 'inferences', 'occurrences']) {
    assert.deepEqual(math[key], plain[key], 'Reading LaTeX changed ' + key);
  }
  const tex = nativeLatex(math);
  assert.match(tex, /反设 \$\\sqrt\{2\} \\in \\mathbb\{Q\}\$/);
  assert.match(tex, /由 .*prime.* 得 .*2 \\mid p/s);
  assert.match(tex, /\\left\(\\frac\{p\}\{2\}\\right\)\^\{2\}/);
  assert.match(tex, /不可能成立，故/);
  assert(!tex.includes('这与'));

  for (const bundle of [math, plain]) {
    const experience = mount(bundle);
    const { root, controller } = experience;
    assert(root.querySelector('.lr-context-explanation').hidden, 'first view keeps the text full width');
    assert(!root.querySelector('.lr-explanation-toggle'));
    const release = bundle.statements.find(item => item.line === 9 && item.source_text.includes('prime_divides_power(p'));
    assert(release, 'known theorem release statement at line 9');
    const selector = bundle.reading_layout
      ? '[data-latex-statement="' + release.id + '"]'
      : '.lr-code-row[data-line="' + release.line + '"] .lr-source-code';
    await root.querySelector(selector).click();
    assert.equal(controller.getSelection().statement, release.id);
    const inspector = root.querySelector('.lr-context-explanation');
    assert(!inspector.hidden && root.querySelector('.lr-with-inspector'));
    await experience.window.dispatch('scroll');
    assert(!inspector.hidden, 'scrolling preserves a selected explanation');
    assert(root.querySelector('.lr-verification-details') && !root.querySelector('.lr-verification-details').open);
    const usedBy = root.querySelector('.lr-used-by');
    assert(usedBy, 'the actual published theorem result has a later user');
    const user = usedBy.querySelector('[data-statement]');
    const target = bundle.statements.find(item => item.id === user.dataset.statement);
    assert(target.cited_fact_ids.some(id => release.produced_fact_ids.includes(id)));
    await user.click();
    assert.equal(controller.getSelection().statement, target.id);
    await root.querySelector('.lr-back').click();
    assert.equal(controller.getSelection().statement, release.id);
    await root.querySelector('.lr-step-next').click();
    assert(controller.getSelection().focusLine > release.line);
    await root.trigger('keydown', { key: 'k' });
    assert.equal(controller.getSelection().statement, release.id);
    await root.trigger('keydown', { key: 'Escape' });
    assert(root.querySelector('.lr-context-explanation').hidden);
    if(bundle.reading_layout){
      const density=root.querySelector('.lr-proof-detail');
      assert(density);
      density.value='outline';await density.trigger('change');
      assert(root.querySelector('.lr-outline-hidden'));
      assert(root.querySelector('[data-latex-statement="'+release.id+'"]:not(.lr-outline-hidden)'));
    }
    controller.destroy();
  }

  const prose = '# Motivation\n\n"""\n## A boxed example\n\nA real number $x$ satisfies a simple identity.\n\n<script>not executable</script>\n"""\nhave x R\nx = x\n';
  const document = compile(prose, true);
  const store = new Map(), initial = mount(document, store, true);
  assert(initial.root.querySelector('.lr-reading-prose h3').textContent.includes('boxed example'));
  assert(initial.root.querySelector('.lr-reading-prose').textContent.includes('Motivation'));
  assert(!initial.root.querySelector('.lr-reading-prose script'));
  assert.match(nativeLatex(document), /\\\[\s*x = x\s*\\\]/);
  assert(!initial.root.querySelector('.lr-ide-input'));
  const markers = initial.root.querySelectorAll('.lr-math-symbol-token');
  assert(markers.length >= 2, 'real KaTeX markup must preserve symbol-level controls');
  const symbol = markers.at(-1).dataset.symbol;
  assert(document.occurrences.some(item => item.symbol_id === symbol));
  await markers.at(-1).click();
  assert.equal(initial.controller.getSelection().symbol, symbol);
  assert(initial.root.querySelectorAll('.lr-math-symbol-token.lr-symbol-selected').length >= 2);
  await initial.root.querySelector('.lr-edit-mode').click();
  const editor = initial.root.querySelector('.lr-ide-input');
  assert.equal(editor.value, prose);
  editor.value += '1=1\n';await editor.trigger('input');
  await initial.root.querySelector('.lr-edit-mode').click();
  assert(initial.root.querySelector('.lr-draft-source'));
  assert(!initial.root.querySelector('.lr-manuscript'));
  initial.controller.destroy();
  const resumed = mount(document, store, true);
  assert.equal(resumed.root.querySelector('.lr-ide-input').value, prose + '1=1\n');
  await resumed.root.querySelector('.lr-check').click();
  await resumed.root.querySelector('.lr-edit-mode').click();
  assert(resumed.root.querySelector('.lr-manuscript'));
  resumed.controller.destroy();
  const rejected = mount(compile('1 / 0 = 0', false, 1));
  await rejected.root.querySelector('.lr-inline-failure').click();
  assert(rejected.root.querySelector('.lr-detail-body .lr-failure-summary').textContent.includes('条件'));
  assert.match(rejected.root.querySelector('.lr-detail-body').textContent, /0\s*(?:!=|≠)\s*0/);
  rejected.controller.destroy();
  console.log('Textbook proof navigation, mathematical prose and symbol links, and editable drafts passed.');
}

run().catch(error => { console.error(error); process.exitCode = 1; });
