#!/usr/bin/env python3
import json,os,pathlib,resource,signal,subprocess,sys,time,datetime
run=pathlib.Path('/private/tmp/mm-lean-verify-20261010')
tool='/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/.tools/lean-4.35.0-rc4-darwin_aarch64/bin'
label=sys.argv[1]
command=sys.argv[2:]
env={'PATH':tool+':/Library/Frameworks/Python.framework/Versions/3.13/bin:/usr/bin:/bin:/usr/sbin','TMPDIR':str(run/'tmp'),'LANG':'C.UTF-8','GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':'/dev/null'}
argv=['/usr/bin/sandbox-exec','-f',str(run/'audit/isolation.sb'),*command]
def limits():
    resource.setrlimit(resource.RLIMIT_CPU,(1200,1200))
    resource.setrlimit(resource.RLIMIT_FSIZE,(2*1024**3,2*1024**3))
record={'argv':argv,'cwd':str(run/'sources/proof'),'environment':env,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limits':{'monitored_descendant_RSS_bytes':10*1024**3,'per_process_CPU_seconds':1200,'per_file_bytes':2*1024**3,'inherited_stack_limit_bytes':8372224,'wall_seconds':1800}}
started=time.monotonic()
with (run/'logs'/f'{label}.log').open('wb') as out:
    p=subprocess.Popen(argv,cwd=run/'sources/proof',env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
    peak=0
    while p.poll() is None:
        rows=subprocess.check_output(['/bin/ps','-e','-o','pid=,ppid=,rss='],text=True).splitlines()
        data=[tuple(map(int,row.split())) for row in rows if len(row.split())==3]
        descendants={p.pid}
        while True:
            expanded=descendants | {pid for pid,ppid,rss in data if ppid in descendants}
            if expanded==descendants:break
            descendants=expanded
        rss=sum(rss*1024 for pid,ppid,rss in data if pid in descendants)
        peak=max(peak,rss)
        why='RSS_limit' if rss>10*1024**3 else 'wall_timeout' if time.monotonic()-started>1800 else None
        if why:
            for pid in descendants:
                try:os.kill(pid,signal.SIGKILL)
                except ProcessLookupError:pass
            p.wait();record['status']=why;break
        time.sleep(1)
    record['exit_code']=p.returncode
    record['peak_monitored_descendant_RSS_bytes']=peak
record['elapsed_seconds']=time.monotonic()-started
(run/'logs'/f'{label}.json').write_text(json.dumps(record,indent=2)+'\n')
print((run/'logs'/f'{label}.log').read_text(errors='replace'))
print(json.dumps(record,indent=2))
sys.exit(record['exit_code'])
