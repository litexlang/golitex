"""Check finite event probability, independent callers and installed std."""
from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import runpy
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def run(binary, path, *, bundled=False, cwd=ROOT):
    env = dict(os.environ)
    env.pop('LITEX_STD_PATH', None)
    if not bundled:
        env['LITEX_STD_PATH'] = str(ROOT/'std')
    started = time.monotonic()
    result = subprocess.run([str(binary), '-lang', 'en', '-strict', '-f', str(path)],
                            cwd=cwd, env=env, capture_output=True, text=True, timeout=300)
    output = json.loads(result.stdout)
    assert output['kind'] == 'run'
    assert not output['session_terminated'] and output['termination'] is None
    assert output['statement_results']
    return result.returncode, output, round(time.monotonic()-started, 3)


def check(exit_code, output, expected_phase):
    statements = output['statement_results']
    if expected_phase is None:
        assert exit_code == 0 and output['run_result'] == 'success', output['errors']
        assert not output['errors']
        assert all(s['statement_result'] == 'accepted' for s in statements)
    else:
        assert exit_code == 1 and output['run_result'] == 'failure', output['errors']
        assert all(s['statement_result'] == 'accepted' for s in statements[:-1])
        assert statements[-1]['statement_result'] == 'rejected'
        assert len(output['errors']) == 1, output['errors']
        error = output['errors'][0]
        assert error['statement_index'] == len(statements)-1, error
        assert error['phase'] == expected_phase, error
        assert error['phase'] not in ('parse', 'tokenize', 'store')


def main(binary, output_dir):
    records = []
    if output_dir:
        output_dir.mkdir(parents=True, exist_ok=True)

    def save(label, path, result, expected_phase, bundled=False):
        exit_code, output, seconds = result
        if output_dir:
            (output_dir/(label+'.json')).write_text(json.dumps(output, indent=2)+'\n')
        check(exit_code, output, expected_phase)
        records.append({'label': label, 'path': str(path), 'exit_code': exit_code,
                        'run_result': output['run_result'], 'seconds': seconds,
                        'statements': len(output['statement_results']),
                        'expected_phase': expected_phase, 'bundled': bundled,
                        'errors': output['errors']})
        print(f'{label}: {output["run_result"]}, {len(output["statement_results"])} statements, {seconds}s', flush=True)

    positives = {'source': ROOT/'std/probability/main.lit',
                 'finite-events': HERE/'main.lit',
                 'generic-contracts': HERE/'contracts/main.lit',
                 'isolated-readme': HERE/'readme/main.lit'}
    negatives = json.loads((HERE/'negative/expected.json').read_text())
    jobs = [(name, path, None) for name, path in positives.items()]
    jobs += [(name, HERE/'negative'/name/'main.lit', phase) for name, phase in negatives.items()]
    pool = ThreadPoolExecutor(max_workers=4)
    try:
        pending = {pool.submit(run, binary, path): (name, path, phase) for name, path, phase in jobs}
        for future in as_completed(pending):
            name, path, phase = pending[future]
            save(name, path, future.result(), phase)
    finally:
        pool.shutdown(wait=True, cancel_futures=True)

    package = runpy.run_path(str(ROOT/'.github/scripts/release/package_std.py'))
    payload = {'std/'+p.relative_to(ROOT/'std').as_posix() for p in package['source_files'](ROOT/'std')}
    assert 'std/probability/main.lit' in payload
    ns = '{http://schemas.microsoft.com/wix/2006/wi}'
    wix = ET.parse(ROOT/'wix/std.wxs')
    wix_payload = {n.attrib['Source'].replace('\\', '/') for n in wix.findall('.//'+ns+'File')}
    assert payload == wix_payload, payload ^ wix_payload
    components = [n.attrib['Id'] for n in wix.findall('.//'+ns+'Component')]
    refs = [n.attrib['Id'] for n in wix.findall('.//'+ns+'ComponentRef')]
    assert len(components) == len(set(components)) and sorted(components) == sorted(refs)
    print(f'std/WiX: {len(payload)} matching files and component references', flush=True)
    with tempfile.TemporaryDirectory(prefix='litex-probability-install-') as temporary:
        base = Path(temporary)
        for label, exe_dir, std_dir in [('archive', 'archive', 'archive/std'),
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
            save(label, path, run(installed_binary, path, bundled=True,
                                 cwd=path.parent), None, bundled=True)
    summary = {'records': records, 'focused_cli_checks': len(records),
               'negative_controls': len(negatives), 'std_payload_files': len(payload)}
    if output_dir:
        (output_dir/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(f'{len(records)} focused probability CLI checks passed', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, default=ROOT/'target/release/litex')
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    main(args.binary.resolve(), args.output_dir.resolve() if args.output_dir else None)
