import datetime
import hashlib
import json
import pathlib
import subprocess
import time

run = pathlib.Path('/private/tmp/mm-lean-published-20261011')
root = run / 'sources/site/proofs/maximum-modulus/lean'
out = run / 'audit/exports'
out.mkdir(exist_ok=True)
targets = [
    'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind',
    'MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii',
    'propext', 'Classical.choice', 'Quot.sound',
    'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod',
    'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight',
    'String.ofList', 'Char.ofNat', 'List', 'eagerReduce', 'Nat', 'String', 'String.mk',
    'Char', 'optParam', 'autoParam', 'semiOutParam', 'outParam'
]
records = []
for label, module in [('challenge', 'MaximumModulus.Audit.ComparatorChallenge'),
                      ('solution', 'MaximumModulus.AllRadii')]:
    build = ['lake', 'build', '+' + module]
    start = time.monotonic()
    with (out / (label + '-build.log')).open('wb') as log:
        result = subprocess.run(build, cwd=root, stdout=log, stderr=subprocess.STDOUT)
    records.append({'argv': build, 'cwd': str(root), 'exit_code': result.returncode,
                    'elapsed_seconds': time.monotonic() - start})
    if result.returncode:
        (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        raise SystemExit(result.returncode)
    command = ['lake', 'env', 'leanexport', module, '--', *targets]
    start = time.monotonic()
    with (out / (label + '.ndjson')).open('wb') as data, (out / (label + '-export.log')).open('wb') as log:
        result = subprocess.run(command, cwd=root, stdout=data, stderr=log)
    data = out / (label + '.ndjson')
    records.append({'argv': command, 'cwd': str(root), 'exit_code': result.returncode,
                    'elapsed_seconds': time.monotonic() - start, 'bytes': data.stat().st_size,
                    'sha256': hashlib.file_digest(data.open('rb'), 'sha256').hexdigest(),
                    'module': module})
    (out / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
    print(label, result.returncode, data.stat().st_size, flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
