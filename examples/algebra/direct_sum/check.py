"""Check source internal direct sums, imported contracts, controls and std installation."""
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
POSITIVES = [ROOT/'std/algebra/direct_sum.lit', HERE/'main.lit', HERE/'contracts.lit', HERE/'boundaries/main.lit', HERE/'idempotent/main.lit']
NEGATIVES = {
    'sum_without_left_subspace': 'goal_well_defined',
    'sum_without_right_subspace': 'goal_well_defined',
    'projection_without_full_sum': 'goal_well_defined',
    'projection_without_zero_intersection': 'goal_well_defined',
    'uniqueness_without_intersection': 'premise',
    'uniqueness_without_equal_sums': 'premise',
    'least_without_containment': 'premise',
    'least_without_target_subspace': 'premise',
    'dimension_without_ambient_finiteness': 'goal_well_defined',
    'dimension_without_left_finiteness': 'goal_well_defined',
    'dimension_without_right_finiteness': 'goal_well_defined',
    'equal_dimension_without_equal_sets': 'premise',
    'split_without_linearity': 'premise',
    'split_without_idempotence': 'premise',
    'overlapping_summands': 'search_proof',
    'nonspanning_summands': 'search_proof',
    'oblique_wrong_left': 'search_proof',
    'oblique_wrong_right': 'search_proof',
    'swapped_pair': 'search_proof',
    'projection_wrong_vector_domain': 'well_defined',
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
            target = OUTPUT_DIR/f'gate-{len(RECORDS)+1:02d}.json'
            target.write_text(json.dumps(output, indent=2)+'\n')
            entry['output'] = str(target)
        RECORDS.append(entry)
    return result, output


def assert_positive(result, output):
    assert result.returncode == 0 and output['run_result'] == 'success', output['errors']
    assert not output['errors']
    assert all(s['statement_result']=='accepted' for s in output['statement_results'])


def assert_negative(name, result, output):
    assert result.returncode == 1 and output['run_result']=='failure', (name, output['errors'])
    statements = output['statement_results']
    assert all(s['statement_result']=='accepted' for s in statements[:-1]), (name, output['errors'])
    assert statements[-1]['statement_result']=='rejected'
    assert len(output['errors'])==1, (name, output['errors'])
    error = output['errors'][0]
    assert error['statement_index']==len(statements)-1, (name, error)
    assert error['phase']==NEGATIVES[name], (name, error)
    assert error['phase'] not in ('parse', 'tokenize')


def installed_checks():
    spec = importlib.util.spec_from_file_location('package_std', ROOT/'.github/scripts/release/package_std.py')
    package = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(package)
    payload = {'std/'+p.relative_to(ROOT/'std').as_posix() for p in package.source_files(ROOT/'std')}
    assert {'std/algebra/direct_sum.lit'} <= payload
    wix = ET.parse(ROOT/'wix/std.wxs')
    wix_payload = {n.attrib['Source'].replace('\\','/') for n in wix.findall('.//{http://schemas.microsoft.com/wix/2006/wi}File')}
    assert wix_payload == payload, wix_payload ^ payload
    ns = '{http://schemas.microsoft.com/wix/2006/wi}'
    components = [n.attrib['Id'] for n in wix.findall('.//'+ns+'Component')]
    refs = [n.attrib['Id'] for n in wix.findall('.//'+ns+'ComponentRef')]
    assert len(components)==len(set(components)) and sorted(components)==sorted(refs)
    print(f'std/WiX payload equality: {len(payload)} files', flush=True)
    with tempfile.TemporaryDirectory(prefix='litex-direct-sums-install-') as temporary:
        base = Path(temporary)
        for label, exe_dir, std_dir in [('archive','archive','archive/std'),('shared-data','prefix/bin','prefix/share/litex/std')]:
            directory = base/exe_dir
            directory.mkdir(parents=True, exist_ok=True)
            binary = directory/BINARY.name
            shutil.copy2(BINARY, binary)
            package.copy_std(ROOT/'std', base/std_dir)
            project = base/(label+'-project')
            for name in ('direct_sum', 'dimension_extension'):
                shutil.copytree(HERE.parent/name, project/name,
                                ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
            result, output = run(project/'direct_sum/main.lit', binary=binary,
                                 cwd=project/'direct_sum', bundled=True)
            assert_positive(result, output)
            print(f'{label}: actual std imported without LITEX_STD_PATH', flush=True)
    return len(payload)


def main():
    with ThreadPoolExecutor(max_workers=2) as pool:
        for path, (result, output) in zip(POSITIVES, pool.map(run, POSITIVES)):
            assert_positive(result, output)
            print(f'{path.relative_to(ROOT)}: {len(output["statement_results"])} accepted', flush=True)
        paths = [HERE/'negative'/name/'main.lit' for name in NEGATIVES]
        for name, (result, output) in zip(NEGATIVES, pool.map(run, paths)):
            assert_negative(name, result, output)
            print(f'{name}: final statement rejected at {NEGATIVES[name]}', flush=True)
    installed_checks()
    print(f'{len(POSITIVES)+len(NEGATIVES)+2} focused direct-sum CLI checks passed', flush=True)


if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, default=BINARY)
    BINARY = parser.parse_args().binary.resolve()
    main()
