'use strict';

const assert = require('node:assert/strict');
const { execFileSync } = require('node:child_process');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const katex = require('../vendor/katex/katex.min.js');
const { createDOM } = require('./dom.cjs');

const binary = path.resolve(process.argv[2] || 'target/release/litex');
const rootPath = path.resolve(__dirname, '../../../..');
const reader = fs.readFileSync(path.join(__dirname, '../reader.js'), 'utf8');

function compile(file) {
  const bundle = JSON.parse(execFileSync(binary, [
    '-reading', '-json', '-strict', '-lang', 'en', '-f', path.join(rootPath, file)
  ], { encoding: 'utf8', maxBuffer: 256 * 1024 * 1024 }));
  assert.equal(bundle.run_result, 'success');
  assert.equal(bundle.sources[0].content, fs.readFileSync(path.join(rootPath, file), 'utf8'));
  return bundle;
}

function mount(bundle, locale, editable) {
  const dom = createDOM(), root = dom.root(), pending = new Map();
  let serial = 0;
  dom.window.katex = { render(tex, node, options) {
    katex.renderToString(tex, options);
    node.textContent = tex;
  }};
  vm.runInContext(reader, vm.createContext({
    ...dom, console, URL, TextEncoder,
    setTimeout(fn) { pending.set(++serial, fn); return serial; },
    clearTimeout(id) { pending.delete(id); }
  }));
  const controller = dom.window.LitexReading.mount(root, {
    document: bundle, locale, ...(editable ? { onCheck: async () => bundle } : {})
  });
  return {
    root, controller,
    async hover(line, selector, index = 0) {
      await root.trigger('keydown', { key: 'Escape' });
      const row = root.querySelector('.lr-code-row[data-line="' + line + '"]');
      assert(row, 'source line ' + line);
      const target = row.querySelectorAll(selector)[index];
      assert(target, selector + ' at line ' + line);
      if (editable) {
        dom.document.elementFromPoint = () => target;
        await root.querySelector('.lr-ide-input').trigger('pointermove', { clientX: 90, clientY: 60 });
      } else {
        await target.trigger('pointermove');
        await target.trigger('mouseenter');
      }
      for (let round = 0; round < 3; round++) for (const [id, fn] of [...pending]) {
        if (pending.delete(id)) await fn();
      }
      const proof = root.querySelector('.lr-proof-popover .lr-proof-evidence');
      assert(proof, 'proof bubble at line ' + line);
      return proof;
    }
  };
}

function sourceLine(bundle, line) {
  const index = bundle.sources[0].content.split('\n').findIndex(value => value.trim() === line);
  assert(index >= 0, line);
  return index + 1;
}

function inspect(proof, math, ...rules) {
  const goal = proof.querySelector('.lr-calculus-formula');
  assert(goal, proof.textContent.slice(0, 350));
  assert.equal(goal.parentNode.children[0], goal, 'formula comes first');
  assert.match(goal.textContent, math);
  const applications = proof.querySelectorAll('.lr-calculus-proof .lr-proof-rule-name').map(node => node.textContent);
  assert.deepEqual(applications, rules);
  const wd = proof.querySelector('.lr-atomic-wd');
  assert(wd && !wd.open, 'domain checks are collapsed');
  assert.equal(wd.parentNode.children.at(-1), wd, 'domain checks come last');
  return wd;
}

async function run() {
  const folder = 'examples/proof_nodes/equal/by_builtin_strategy/';
  const derivative = compile(folder + 'derivative_value.lit');
  const integral = compile(folder + 'riemann_integral_value.lit');
  const aliases = compile('examples/wd/builtin_short_names.lit');
  const demo = compile('examples/reading/derivatives_and_integrals.lit');
  const original = [derivative, integral, aliases].map(value => JSON.stringify(value));
  for (const [locale, editable] of [['zh', true], ['en', false]]) {
    const diff = mount(derivative, locale, editable);
    const diffProof = await diff.hover(sourceLine(derivative, 'deriv(square,3)=6'), '.lr-source-code');
    const diffWD = inspect(diffProof, /\\prime.*3.*6/, 'DerivativeValue', 'PointwiseDerivative');
    const diffSteps = diffProof.querySelector('.lr-calculus-steps');
    assert(diffSteps && !diffSteps.open);
    await diffSteps.querySelector('summary').click();
    assert(diffSteps.querySelector('[data-constructor="Mul"]'));
    await diffWD.querySelector('summary').click();
    assert(diffWD.querySelector('.lr-proof-step'), 'domain conditions have their own proof');
    if (editable) assert.equal(diff.root.querySelector('.lr-ide-input').value, derivative.sources[0].content);
    diff.controller.destroy();

    const area = mount(integral, locale, editable);
    const direct = await area.hover(sourceLine(integral, 'integral(p,0,1)=3'), '.lr-chain-equality');
    inspect(direct, /\\int_\{0\}\^\{1\}.*3/, 'RiemannIntegralValue', 'StructuralRiemannIntegral');
    const areaSteps = direct.querySelector('.lr-calculus-steps');
    await areaSteps.querySelector('summary').click();
    assert(areaSteps.querySelector('[data-constructor="NaturalPower"]'));

    const reverse = await area.hover(sourceLine(integral, 'integral(p,1,0)=-3'), '.lr-chain-equality');
    inspect(reverse, /\\int_\{1\}\^\{0\}.*-3/, 'RiemannIntegralSelectedValue');
    const reference = reverse.querySelector('.lr-calculus-proof .lr-fact-link');
    const premise = integral.facts.find(fact => fact.id === reference?.dataset.fact);
    assert.equal(premise?.line, sourceLine(integral, '$has_riemann_integral(p,1,0,-3)'));
    assert(reference.querySelector('.lr-calculus-formula'), 'cited value is typeset');
    await area.root.querySelector('.lr-proof-pin').click();
    const old = area.controller.getSelection();
    const pinned = area.root.querySelector('.lr-detail-body .lr-calculus-proof .lr-fact-link');
    assert.equal(pinned.dataset.fact, premise.id);
    await pinned.click();
    assert.equal(area.controller.getSelection().fact, premise.id);
    await area.root.querySelector('.lr-back').click();
    assert.deepEqual(area.controller.getSelection(), old);
    area.controller.destroy();

    const chains = mount(aliases, locale, editable);
    const chainLine = sourceLine(aliases, 'deriv(square,3)=derivative(square,3)=6');
    const first = await chains.hover(chainLine, '.lr-chain-equality', 0);
    const firstFormula = first.querySelector('.lr-calculus-formula').textContent;
    assert.equal((firstFormula.match(/\\prime/g) || []).length, 2);
    const second = await chains.hover(chainLine, '.lr-chain-equality', 1);
    inspect(second, /\\prime.*3.*6/, 'DerivativeSelectedValue');
    assert.equal((second.querySelector('.lr-calculus-formula').textContent.match(/\\prime/g) || []).length, 1);
    const compared = await chains.hover(sourceLine(aliases, 'integral(total,0,1)=4/3'), '.lr-chain-equality');
    inspect(compared, /\\int_\{0\}\^\{1\}.*\\frac\{4\}\{3\}/, 'RiemannIntegralSelectedValue');
    assert(compared.querySelector('.lr-calculus-proof details'), 'retain a nontrivial candidate-value comparison');
    chains.controller.destroy();
  }
  const demoView = mount(demo, 'zh', true);
  for (const [source, math, expected] of [
    ['deriv(square, 4) = 8', /\\prime.*4.*8/, ['DerivativeSelectedValue']],
    ['deriv(affine_power, a) = 15 * (3*a + 1)^4', /\\prime.*15/, ['DerivativeValue', 'PointwiseDerivative']],
    ['integral(odd_power, -1, 1) = 0', /\\int_\{-1\}\^\{1\}.*0/, ['RiemannIntegralValue', 'StructuralRiemannIntegral']]
  ]) inspect(await demoView.hover(sourceLine(demo, source), '.lr-chain-equality'), math, ...expected);
  demoView.controller.destroy();

  const polynomial = compile('tests/fixtures/compile_to_lean/polynomial_integrals.lit');
  const polyView = mount(polynomial, 'en', false);
  const polyProof = await polyView.hover(sourceLine(polynomial, 'integral(fn(x R) R {(x+1)^2},0,1)=7/3'), '.lr-chain-equality');
  inspect(polyProof, /\\int_\{0\}\^\{1\}.*\\frac\{7\}\{3\}/, 'RiemannIntegralValue', 'StructuralRiemannIntegral');
  const polySteps = polyProof.querySelector('.lr-calculus-steps');
  assert.match(polySteps.querySelector('summary').textContent, /Polynomial expansion/);
  await polySteps.querySelector('summary').click();
  assert(polySteps.querySelector('[data-constructor="Polynomial"]'));
  assert(polySteps.querySelector('[data-constructor="NaturalPower"]'));
  polyView.controller.destroy();
  assert.deepEqual([derivative, integral, aliases].map(value => JSON.stringify(value)), original);
  console.log('Calculus proofs passed in the editable Chinese and read-only English source viewers.');
}

run().catch(error => { console.error(error); process.exitCode = 1; });
