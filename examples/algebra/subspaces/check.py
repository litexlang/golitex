"""Check inherited finite subspaces, imported callers and installed std layouts."""
from concurrent.futures import ThreadPoolExecutor
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import threading
import time
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BINARY = ROOT / 'target/release/litex'
POSITIVES = [ROOT/'std/algebra/subspace.lit', HERE/'main.lit', HERE/'contracts.lit']
NEGATIVES = {
    'finite_without_ambient_finiteness': 'premise',
    'ambient_independence_missing': 'premise',
    'intrinsic_independence_missing': 'premise',
    'unequal_combination_values': 'conclusion',
    'subspace_larger_than_ambient': 'conclusion',
    'restricted_space_without_subspace': 'well_defined',
    'restricted_add_without_subspace': 'well_defined',
    'restricted_smul_without_subspace': 'well_defined',
    'dimension_without_subspace_finiteness': 'well_defined',
    'inclusion_argument_outside_domain': 'well_defined',
    'sequence_inclusion_wrong_direction': 'premise',
    'axis_dimension_two': 'search_proof',
    'zero_dimension_positive': 'search_proof',
}
RECORDS = []
OUTPUT_DIR = None
LOCK = threading.Lock()


def run(path, *, binary=None, cwd=ROOT, bundled=False):
    binary = BINARY if binary is None else binary
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
    entry = {'path': str(path), 'bundled': bundled, 'exit_code': result.returncode,
             'run_result': output['run_result'], 'statements': len(output['statement_results']),
             'seconds': round(time.monotonic()-started, 3), 'errors': output['errors'],
             'session_terminated': output['session_terminated'], 'termination': output['termination']}
    with LOCK:
        if OUTPUT_DIR:
            target = OUTPUT_DIR/f'final-{len(RECORDS)+1:02d}.json'
            target.write_text(json.dumps(output, indent=2)+'\n')
            entry['output'] = str(target)
        RECORDS.append(entry)
    return result, output


def assert_positive(result, output):
    assert result.returncode == 0 and output['run_result'] == 'success', output['errors']
    assert not output['errors']
    assert all(s['statement_result']=='accepted' for s in output['statement_results'])


def main():
    with ThreadPoolExecutor(max_workers=2) as pool:
        for path, (r, d) in zip(POSITIVES, pool.map(run, POSITIVES)):
            assert_positive(r, d)
            print(f'{path.relative_to(ROOT)}: {len(d["statement_results"])} accepted', flush=True)
        paths = [(HERE/('concrete_negative' if name in ('axis_dimension_two', 'zero_dimension_positive') else 'negative')/(name+'.lit')) for name in NEGATIVES]
        for (name, phase), (r, d) in zip(NEGATIVES.items(), pool.map(run, paths)):
            assert r.returncode == 1 and d['run_result']=='failure', (name, d['errors'])
            statements = d['statement_results']
            assert all(s['statement_result']=='accepted' for s in statements[:-1]), (name, d['errors'])
            assert statements[-1]['statement_result']=='rejected'
            assert len(d['errors'])==1, (name, d['errors'])
            e=d['errors'][0]
            assert e['statement_index']==len(statements)-1 and e['phase']==phase, (name, e)
            print(f'{name}: final statement rejected at {phase}', flush=True)
    spec = importlib.util.spec_from_file_location('package_std', ROOT/'.github/scripts/release/package_std.py')
    package = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(package)
    payload={'std/'+p.relative_to(ROOT/'std').as_posix() for p in package.source_files(ROOT/'std')}
    assert 'std/algebra/subspace.lit' in payload
    wix=ET.parse(ROOT/'wix/std.wxs')
    wix_payload={n.attrib['Source'].replace('\\','/') for n in wix.findall('.//{http://schemas.microsoft.com/wix/2006/wi}File')}
    assert wix_payload==payload, wix_payload ^ payload
    print(f'std/WiX payload equality: {len(payload)} files', flush=True)
    with tempfile.TemporaryDirectory(prefix='litex-subspaces-install-') as temporary:
        base=Path(temporary)
        for label, exe_dir, std_dir in [('archive','archive','archive/std'),('shared-data','prefix/bin','prefix/share/litex/std')]:
            directory=base/exe_dir
            directory.mkdir(parents=True, exist_ok=True)
            binary=directory/BINARY.name
            shutil.copy2(BINARY, binary)
            package.copy_std(ROOT/'std', base/std_dir)
            project=base/(label+'-project')
            shutil.copytree(HERE, project/'subspaces', ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
            shutil.copytree(HERE.parent/'dimension_extension', project/'dimension_extension', ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
            r,d=run(project/'subspaces/main.lit', binary=binary, cwd=project/'subspaces', bundled=True)
            assert_positive(r,d)
            print(f'{label}: actual std imported without LITEX_STD_PATH', flush=True)
    print('18 focused subspace CLI checks passed', flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--binary',type=Path,default=BINARY)
    BINARY=parser.parse_args().binary.resolve()
    main()
