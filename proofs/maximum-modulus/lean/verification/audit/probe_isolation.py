import pathlib,subprocess,socket,json
results={}
try:pathlib.Path('/private/tmp/mm-lean-isolation-read-probe.txt').read_text();results['outside_read']='UNEXPECTED_ALLOWED'
except OSError as e:results['outside_read']=str(e)
try:pathlib.Path('/private/tmp/mm-lean-isolation-write-probe.txt').write_text('harmless probe');results['outside_write']='UNEXPECTED_ALLOWED'
except OSError as e:results['outside_write']=str(e)
try:
 s=socket.socket();s.settimeout(3);s.connect(('1.1.1.1',443));s.close();results['network']='UNEXPECTED_ALLOWED'
except OSError as e:results['network']=str(e)
r=subprocess.run(['/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/.tools/lean-4.35.0-rc4-darwin_aarch64/bin/lean','--version'],capture_output=True,text=True)
results['lean_exit']=r.returncode;results['lean_version']=r.stdout;results['lean_stderr']=r.stderr
print(json.dumps(results,indent=2))
assert all('UNEXPECTED' not in results[k] for k in ['outside_read','outside_write','network'])
assert r.returncode==0
