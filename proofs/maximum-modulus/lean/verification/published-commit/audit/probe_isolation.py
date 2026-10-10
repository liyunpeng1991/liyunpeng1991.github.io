import json, pathlib, subprocess, socket
tests={}
for label,action in [
 ('outside-user-data',lambda:pathlib.Path('/Users/gluon/Documents/ChatGPT/Maximum Modulus/maximum_modulus_points.tex').read_bytes()),
 ('outside-tmp-data',lambda:pathlib.Path('/private/tmp/mm-lean-verify-20261010/audit/targets.json').read_bytes()),
 ('outside-tmp-write',lambda:pathlib.Path('/private/tmp/mm-lean-published-forbidden-probe').write_text('probe')),
 ('network',lambda:socket.create_connection(('1.1.1.1',80),timeout=4))]:
    try:
        action(); tests[label]={'blocked':False}
    except Exception as e:
        reason=getattr(e,'reason',e)
        tests[label]={'blocked':isinstance(reason,OSError) and reason.errno in (1,13),'error':repr(e)}
p=subprocess.run(['/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/.tools/lean-4.35.0-rc4-darwin_aarch64/bin/lean','--version'],capture_output=True,text=True)
tests['trusted-toolchain']={'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
pathlib.Path('/private/tmp/mm-lean-published-20261011/evidence/isolation-probe.json').write_text(json.dumps(tests,indent=2)+'\n')
print(json.dumps(tests,indent=2))
assert all(v['blocked'] for k,v in tests.items() if k!='trusted-toolchain')
assert p.returncode==0
