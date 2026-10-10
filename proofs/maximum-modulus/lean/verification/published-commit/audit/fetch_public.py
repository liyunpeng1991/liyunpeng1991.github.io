#!/usr/bin/env python3
"""Read-only public Git retrieval; execute no project program."""
import datetime, json, os, pathlib, re, subprocess, sys, time
run = pathlib.Path('/private/tmp/mm-lean-published-20261011')
repo = 'https://github.com/liyunpeng1991/liyunpeng1991.github.io.git'
sha = sys.argv[1]
assert re.fullmatch('[0-9a-f]{40}', sha), 'Expected full commit SHA'
root = run / 'sources/site'
assert not root.exists(), 'Use a new clone; never overwrite a source checkout'
env = {'PATH':'/usr/bin:/bin:/usr/sbin:/sbin', 'GIT_CONFIG_NOSYSTEM':'1',
       'GIT_CONFIG_GLOBAL':'/dev/null', 'GIT_TERMINAL_PROMPT':'0', 'LANG':'C.UTF-8'}
records = []
def command(label, args, permit_failure=False):
    argv=['/usr/bin/git','-c','credential.helper=','-c','core.hooksPath=/dev/null',*args]
    started=time.monotonic()
    record={'argv':argv,'cwd':str(run),'environment':env,
            'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    with (run/'logs'/('fetch-'+label+'.log')).open('wb') as out:
        p=subprocess.run(argv,cwd=run,env=env,stdout=out,stderr=subprocess.STDOUT)
    record.update(exit_code=p.returncode,elapsed_seconds=time.monotonic()-started,
                  log='logs/fetch-'+label+'.log')
    records.append(record)
    (run/'evidence/public-fetch-commands.json').write_text(json.dumps(records,indent=2)+'\n')
    print(label,p.returncode,flush=True)
    if p.returncode and not permit_failure: raise SystemExit(p.returncode)
    return p.returncode
command('clone',['clone','--no-checkout','--depth','1','--filter=blob:none','--',repo,str(root)])
if command('object-before',['-C',str(root),'cat-file','-t',sha],True):
    command('exact-sha',['-C',str(root),'fetch','--depth','1','origin',sha])
command('object',['-C',str(root),'cat-file','-t',sha])
command('checkout',['-C',str(root),'checkout','--detach',sha])
command('head',['-C',str(root),'rev-parse','HEAD'])
command('status',['-C',str(root),'status','--porcelain=v1','--untracked-files=all'])
actual=(run/'logs/fetch-head.log').read_text().strip()
assert actual==sha,(sha,actual)
assert not (run/'logs/fetch-status.log').read_text().strip()
(run/'evidence/public-input.json').write_text(json.dumps({
    'repository':repo,'selected_commit':sha,'actual_HEAD':actual,
    'project_subdirectory':'proofs/maximum-modulus/lean',
    'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'read_only_remote_operations':True},indent=2)+'\n')
