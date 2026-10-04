"""Run explicit positive/negative basic contracts without changing the kernel."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
from module_checks import run_module_checks


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--workdir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=20)
    args=parser.parse_args()
    binary=args.binary.resolve(); manifest=json.loads(args.manifest.read_text())
    suite=args.manifest.resolve().parent
    for case in manifest['cases']:
        source=(suite/case['file']).resolve()
        assert source.is_relative_to(suite) and source.is_file(), case['file']
        case['code']=source.read_text()
    work=args.workdir.resolve(); work.mkdir(parents=True,exist_ok=True)
    identity=hashlib.sha256(binary.read_bytes()).hexdigest()
    jobs=[(case,index) for case in manifest['cases'] for index in range(case.get('repeats',1))]
    assert jobs and len({case['name'] for case in manifest['cases']})==len(manifest['cases'])
    records=[]
    with ThreadPoolExecutor(max_workers=4) as pool:
        records=list(pool.map(lambda job: run_case(args,binary,work,*job),jobs))
    for session in manifest.get('sessions',[]):
        records.append(run_session(args,binary,work,session))
    records.extend(run_module_checks(binary,work))
    for kind in ['eval','file','repo']:
        for valid in [True,False]:
            records.append(run_entry(args,binary,work,kind,valid))
    for lang in ['en','zh']:
        for valid in [True,False]:
            case=dict(contracts=['C03'],name=f'language-{lang}-{valid}',code='1 + 2 = '+('3' if valid else '4'),expected=valid,statements=[valid],lang=lang)
            records.append(run_case(args,binary,work,case,0))
    for name, flags, code in [('unknown-flag',['-does-not-exist'],2),('missing-file',['-f',str(work/'missing.lit')],1)]:
        start=time.monotonic(); proc=subprocess.run([str(binary),*flags],cwd=work,text=True,capture_output=True,timeout=args.timeout)
        records.append(dict(contracts=['C04'],name=name,command=[str(binary),*flags],returncode=proc.returncode,stdout=proc.stdout,stderr=proc.stderr,seconds=time.monotonic()-start,matches=proc.returncode==code and bool(proc.stderr)))
    assert identity==hashlib.sha256(binary.read_bytes()).hexdigest(), 'binary drift invalidates audit'
    for case in manifest['cases']:
        assert (suite/case['file']).read_text()==case['code'], 'fixture drift invalidates audit'
    assert set(manifest['contracts'])=={contract for record in records for contract in record['contracts']}, 'missing contract collection'
    report=dict(schema_version=1,binary=str(binary),binary_sha256=identity,manifest_sha256=hashlib.sha256(args.manifest.read_bytes()).hexdigest(),fixture_hashes={case['file']:hashlib.sha256(case['code'].encode()).hexdigest() for case in manifest['cases']},checks=len(records),passed=sum(r['matches'] for r in records),failed=sum(not r['matches'] for r in records),records=records)
    args.report.parent.mkdir(parents=True,exist_ok=True); args.report.write_text(json.dumps(report,indent=2)+'\n')
    failures=[r for r in records if not r['matches']]
    for r in failures:
        print('FAIL',r['name'],r.get('errors',[]),r.get('returncode'))
    print(f'{report["checks"]} checks; {report["passed"]} pass; {report["failed"]} fail')
    return bool(failures)


def run_case(args,binary,work,case,index):
    mode=case.get('input_mode','file' if case['code'].lstrip().startswith('-') else 'eval')
    if mode=='file':
        fixture=work/(case['name']+'.lit'); fixture.write_text(case['code'])
    command=[str(binary),'-strict','-lang',case.get('lang','en'),'-f' if mode=='file' else '-e',str(fixture) if mode=='file' else case['code']]
    start=time.monotonic(); errors=[]; data=None
    record=dict(contracts=case['contracts'],name=case['name'],repeat=index,code=case['code'],expected=case['expected'],command=command)
    try:
        proc=subprocess.run(command,cwd=work,text=True,capture_output=True,timeout=args.timeout)
        record.update(returncode=proc.returncode,stdout=proc.stdout,stderr=proc.stderr)
        try: data=json.loads(proc.stdout)
        except ValueError: errors.append('invalid or missing JSON')
        if isinstance(data,dict):
            data=normalize(data)
            if data.get('success') is not case['expected']: errors.append('wrong success')
            if proc.returncode != (0 if data.get('success') is True else 1): errors.append('exit/JSON disagreement')
            actual=[s.get('success') for s in data.get('statement_results',[])]
            if 'statements' in case and actual!=case['statements']: errors.append(f'statements {actual} != {case["statements"]}')
            if bool(data.get('session_error'))!=case.get('session_error',False): errors.append('unexpected session-error state')
            if 'values' in case:
                values=[s['evaluated_object'].replace(' ','') for s in data.get('statement_results',[]) if 'evaluated_object' in s]
                if values!=case['values']: errors.append(f'values {values} != {case["values"]}')
        if proc.stderr: errors.append('unexpected stderr')
        if proc.returncode not in (0,1): errors.append('abnormal exit')
    except subprocess.TimeoutExpired as exc:
        errors.append('timeout'); record.update(returncode=None,stdout=exc.stdout.decode() if isinstance(exc.stdout,bytes) else exc.stdout,stderr=exc.stderr.decode() if isinstance(exc.stderr,bytes) else exc.stderr)
    record.update(seconds=time.monotonic()-start,output=data,errors=errors,matches=not errors)
    return record


def run_session(args,binary,work,session):
    command=[str(binary),'-strict']; source='\n\n'.join(session['frames'])+'\n\nexit\n'
    start=time.monotonic(); errors=[]
    try:
        proc=subprocess.run(command,input=source,cwd=work,text=True,capture_output=True,timeout=args.timeout)
        responses=[m=='success' for m in re.findall(r'^(?:(?:litex> |\.\.\. ))*(success|error)$',proc.stdout,re.M)]
        if responses!=session['responses']: errors.append(f'frames {responses} != {session["responses"]}')
        if bool(proc.stderr)!=session.get('error',False): errors.append('unexpected session stderr')
        if proc.returncode != (1 if session.get('error',False) else 0): errors.append('unexpected session exit')
        return dict(contracts=session['contracts'],name=session['name'],frames=session['frames'],responses=responses,command=command,returncode=proc.returncode,stdout=proc.stdout,stderr=proc.stderr,seconds=time.monotonic()-start,errors=errors,matches=not errors)
    except subprocess.TimeoutExpired:
        return dict(contracts=session['contracts'],name=session['name'],frames=session['frames'],matches=False,errors=['timeout'],seconds=time.monotonic()-start)


def run_entry(args,binary,work,kind,valid):
    source='have fn f(x R) R = x + 1\nf(2) = 2 + 1 = '+('3' if valid else '4')+'\n'
    case=dict(contracts=['C01'],name=f'entry-{kind}-{valid}',code=source,expected=valid,statements=[True,valid])
    if kind=='eval': return run_case(args,binary,work,case,0)
    fixture=work/f'entry-{kind}-{valid}'; fixture.mkdir(exist_ok=True)
    path=fixture/'main.lit'; path.write_text(source)
    if kind=='repo': (fixture/'litex.config').write_text('[export]\nmain = "./main.lit"\n')
    command=[str(binary),'-strict','-f' if kind=='file' else '-r',str(path if kind=='file' else fixture)]
    start=time.monotonic()
    try:
        proc=subprocess.run(command,cwd=work,text=True,capture_output=True,timeout=args.timeout); data=json.loads(proc.stdout)
        matches=data.get('success') is valid and proc.returncode==(0 if valid else 1) and not proc.stderr
        if kind=='file': matches=matches and [s['success'] for s in data['statement_results']]==[True,valid]
        return dict(contracts=case['contracts'],name=case['name'],code=source,expected=valid,command=command,returncode=proc.returncode,stdout=proc.stdout,stderr=proc.stderr,output=data,seconds=time.monotonic()-start,matches=matches)
    except (subprocess.TimeoutExpired,ValueError) as exc:
        return dict(contracts=case['contracts'],name=case['name'],code=source,expected=valid,matches=False,errors=[type(exc).__name__],seconds=time.monotonic()-start)


def normalize(value):
    names={'成功':'success','语句结果':'statement_results','会话错误':'session_error','求值结果':'evaluated_object'}
    if isinstance(value,dict): return {names.get(k,k):normalize(v) for k,v in value.items()}
    if isinstance(value,list): return [normalize(v) for v in value]
    return value


if __name__=='__main__':
    raise SystemExit(main())
