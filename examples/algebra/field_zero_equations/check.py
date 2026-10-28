"""Check zero-coefficient field equations."""
from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import json
from pathlib import Path
import re
import runpy
import shutil
import tempfile
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
COMMON = runpy.run_path(str(ROOT/'examples/probability/finite_events/check.py'))


def main(binary, output_dir):
    assert ROOT == COMMON['ROOT']
    output_dir.mkdir(parents=True, exist_ok=True)
    records = []

    def save(label, path, result, phase, installed=False):
        exit_code, output, seconds = result
        (output_dir/(label+'.json')).write_text(json.dumps(output, indent=2)+'\n')
        COMMON['check'](exit_code, output, phase)
        records.append({'label': label, 'path': str(path), 'exit_code': exit_code,
                        'run_result': output['run_result'], 'seconds': seconds,
                        'statements': len(output['statement_results']),
                        'expected_phase': phase, 'installed': installed,
                        'errors': output['errors']})
        print(f'{label}: expected {output["run_result"]}, {seconds}s', flush=True)

    readme = (HERE/'README.md').read_text()
    snippets = re.findall(r'```litex\n(.*?)\n```', readme, re.S)
    assert snippets == [(HERE/'readme/main.lit').read_text().strip()]
    positives = {'source': ROOT/'std/algebra/field.lit',
                 'contracts': HERE/'contracts/main.lit',
                 'actual': HERE/'main.lit',
                 'readme': HERE/'readme/main.lit',
                 'legacy-vector-spaces': HERE.parent/'vector_spaces/main.lit'}
    negatives = json.loads((HERE/'negative/expected.json').read_text())
    jobs = [(label, path, None) for label, path in positives.items()]
    jobs += [(label, HERE/'negative'/label/'main.lit', phase)
             for label, phase in negatives.items()]
    with ThreadPoolExecutor(max_workers=4) as pool:
        pending = {pool.submit(COMMON['run'], binary, path): (label, path, phase)
                   for label, path, phase in jobs}
        for future in as_completed(pending):
            label, path, phase = pending[future]
            save(label, path, future.result(), phase)

    package = runpy.run_path(str(ROOT/'.github/scripts/release/package_std.py'))
    payload = {'std/'+p.relative_to(ROOT/'std').as_posix()
               for p in package['source_files'](ROOT/'std')}
    ns = '{http://schemas.microsoft.com/wix/2006/wi}'
    wix = ET.parse(ROOT/'wix/std.wxs')
    assert payload == {n.attrib['Source'].replace('\\', '/')
                       for n in wix.findall('.//'+ns+'File')}
    components = [n.attrib['Id'] for n in wix.findall('.//'+ns+'Component')]
    references = [n.attrib['Id'] for n in wix.findall('.//'+ns+'ComponentRef')]
    assert len(components) == len(set(components))
    assert sorted(components) == sorted(references)
    with tempfile.TemporaryDirectory(prefix='litex-field-zero-equations-') as temporary:
        base = Path(temporary)
        for label, exe_dir, std_dir in [
                ('archive', 'archive', 'archive/std'),
                ('shared-data', 'prefix/bin', 'prefix/share/litex/std')]:
            directory = base/exe_dir
            directory.mkdir(parents=True, exist_ok=True)
            installed_binary = directory/binary.name
            shutil.copy2(binary, installed_binary)
            package['copy_std'](ROOT/'std', base/std_dir)
            project = base/(label+'-project')
            shutil.copytree(HERE, project,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            path = project/'main.lit'
            result = COMMON['run'](installed_binary, path, bundled=True,
                                   cwd=path.parent)
            save(label, path, result, None, installed=True)
    summary = {'records': records, 'focused_cli_checks': len(records),
               'negative_controls': len(negatives),
               'std_payload_files': len(payload)}
    (output_dir/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(f'{len(records)} field-zero-equation CLI checks passed', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, default=ROOT/'target/release/litex')
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    main(args.binary.resolve(), args.output_dir.resolve())
