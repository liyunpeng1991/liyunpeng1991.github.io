#!/usr/bin/env python3
"""Read-only collection of actual copied dependency revisions and tool hashes."""
import datetime
import hashlib
import json
import os
import pathlib
import platform
import shutil
import subprocess

run = pathlib.Path('/private/tmp/mm-lean-published-20261011')
root = run / 'sources/site/proofs/maximum-modulus/lean'
tool = pathlib.Path('/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean/.tools/lean-4.35.0-rc4-darwin_aarch64')

def command(argv, cwd=None):
    p = subprocess.run(argv, cwd=cwd, text=True, capture_output=True, check=False)
    return {'argv': argv, 'cwd': str(cwd) if cwd else None,
            'exit_code': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

manifest = json.loads((root / 'lake-manifest.json').read_text())
dependencies = []
for package in manifest['packages']:
    checkout = root / manifest['packagesDir'] / package['name']
    head = command(['/usr/bin/git', 'rev-parse', 'HEAD'], checkout)
    status = command(['/usr/bin/git', 'status', '--porcelain=v1', '--untracked-files=normal'], checkout)
    dependencies.append({'name': package['name'], 'url': package['url'],
                         'manifest_revision': package['rev'], 'checkout': str(checkout),
                         'actual_revision': head['stdout'].strip(),
                         'revision_matches': head['exit_code'] == 0 and head['stdout'].strip() == package['rev'],
                         'head_command': head, 'status_command': status})

tools = {}
for name in ['lean', 'lake', 'leanchecker', 'leanchecker-paranoid',
             'lean4lean', 'nanoda_bin', 'con-leche', 'con-ron', 'leanexport']:
    path = tool / 'bin' / name
    tools[name] = {'path': str(path), 'exists': path.is_file(),
                   'sha256': sha(path) if path.is_file() else None}

data = {'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'collection_scope': 'read-only actual copied dependency Git metadata, trusted tool hashes, OS metadata; no Lake/Lean proof execution',
        'os': command(['/usr/bin/sw_vers']), 'uname': command(['/usr/bin/uname', '-a']),
        'platform': platform.platform(), 'architecture': platform.machine(),
        'python': {'executable': os.path.realpath(os.sys.executable), 'version': platform.python_version()},
        'elan_in_sanitized_path': shutil.which('elan'),
        'toolchain': (root / 'lean-toolchain').read_text().strip(),
        'lake_manifest_sha256': sha(root / 'lake-manifest.json'),
        'dependencies': dependencies, 'tools': tools,
        'source_state': command(['/usr/bin/git', 'status', '--porcelain=v1'], root)}
(run / 'evidence/dependency-tool-provenance.json').write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps({'all_dependency_revisions_match': all(p['revision_matches'] for p in dependencies),
                  'dependency_count': len(dependencies),
                  'dirty_dependency_checkouts': [p['name'] for p in dependencies if p['status_command']['stdout']],
                  'missing_tools': [name for name, value in tools.items() if not value['exists']],
                  'evidence': str(run / 'evidence/dependency-tool-provenance.json')}, indent=2))

assert all(p["revision_matches"] for p in dependencies), "Dependency revision mismatch"
assert all(not p["status_command"]["stdout"] for p in dependencies), "Dirty dependency"
assert all(t["exists"] for t in tools.values()), "Missing trusted tool"
