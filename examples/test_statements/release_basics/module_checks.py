"""Real module/cache controls; the caller supplies a task-owned work area."""
import hashlib,json,shutil,subprocess,time
from pathlib import Path

def run_module_checks(binary,work):
    root=work/'modules'
    if root.exists():
        shutil.rmtree(root)
    root.mkdir(parents=True)
    area=work
    records=[]

    def write(path,source):
        path.parent.mkdir(parents=True,exist_ok=True); path.write_text(source)

    def run(name,expected,contracts):
        command=[str(binary),'-strict','-r',str(root)]
        start=time.monotonic(); p=subprocess.run(command,cwd=area,text=True,capture_output=True,timeout=20)
        try: data=json.loads(p.stdout)
        except ValueError: data={}
        records.append(dict(name=name,contracts=contracts,expected=expected,command=command,returncode=p.returncode,stdout=p.stdout,stderr=p.stderr,output=data,seconds=time.monotonic()-start,matches=data.get('success') is expected and p.returncode==(0 if expected else 1) and not p.stderr,files={str(f.relative_to(root)):f.read_text() for f in root.rglob('*') if f.is_file() and '__litex_knowledge_base__' not in f.parts}))

    left='let value = 1\nhave fn same(x R) R = x + 1\n'
    right='let value = 2\nhave fn same(x R) R = x + 2\n'
    write(root/'left/litex.config','[export]\nfacts = "./facts.lit"\n')
    write(root/'right/litex.config','[export]\nfacts = "./facts.lit"\n')
    write(root/'left/facts.lit',left); write(root/'right/facts.lit',right)
    config='[import]\nLeft = "./left"\nRight = "./right"\n[export]\nmain = "./main.lit"\n'
    write(root/'litex.config',config)
    source='release obj def Left::facts::value\nrelease obj def Right::facts::value\nrelease obj def Left::facts::same\nrelease obj def Right::facts::same\nLeft::facts::value = 1\nRight::facts::value = 2\nLeft::facts::same(2) = 2 + 1 = 3\nRight::facts::same(2) = 2 + 2 = 4\n'
    write(root/'main.lit',source)
    run('cold-two-same-named-owners',True,['M01','M02'])
    before={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in root.rglob('manifest.json')}
    run('warm-two-same-named-owners',True,['M01','M02'])
    records[-1]['cache_manifests_before']=before
    write(root/'main.lit',source.replace('Right::facts::value = 2','Right::facts::value = 1'))
    run('wrong-owner-value-must-reject',False,['M01'])
    write(root/'main.lit',source)
    write(root/'litex.config',config.replace('Left = "./left"\nRight = "./right"','Right = "./right"\nLeft = "./left"'))
    run('cached-import-order-reversed',True,['M04'])
    write(root/'left/facts.lit',left.replace('value = 1','value = 3'))
    run('changed-source-invalidates-old-conclusion',False,['M03'])
    write(root/'main.lit',source.replace('Left::facts::value = 1','Left::facts::value = 3'))
    run('changed-source-new-conclusion',True,['M03'])
    after={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in root.rglob('manifest.json')}
    records[-1]['cache_manifests_after']=after
    records[-1]['changed_cache']=before!=after
    write(root/'bad/litex.config','[export]\nfacts = "./facts.lit"\n')
    write(root/'bad/facts.lit','let value = 9\n1 = 2\n')
    write(root/'litex.config','[import]\nBad = "./bad"\n[export]\nmain = "./main.lit"\n')
    write(root/'main.lit','1 = 1\n')
    for index in range(2):
        run(f'failed-library-no-cache-{index}',False,['M04'])
        records[-1]['no_failed_library_cache']=not (root/'bad/__litex_knowledge_base__/manifest.json').exists()
        records[-1]['matches'] &= records[-1]['no_failed_library_cache']
    return records
