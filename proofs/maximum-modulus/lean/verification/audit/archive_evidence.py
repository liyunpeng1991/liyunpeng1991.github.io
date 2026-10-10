"""Preserve the completed local audit without changing the production proof."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import shutil
import subprocess

run = Path('/private/tmp/mm-lean-verify-20261010')
workflow = Path('/private/tmp/mm-lean-verify-workflow-20261010')
project = Path('/Users/gluon/Documents/ChatGPT/Maximum Modulus/lean')
destination = project / 'verification'
report = (run / 'audit/report.md').read_text()
assert report.startswith('**Overall verdict: Verification passed')
comparator = json.loads((run / 'logs/comparator-paranoid-01.json').read_text())
assert comparator['exit_code'] == 0
destination.mkdir(exist_ok=True)

for name in ('audit', 'evidence', 'logs'):
    shutil.copytree(run / name, destination / name, dirs_exist_ok=True)
shutil.copytree(workflow, destination / 'workflow', dirs_exist_ok=True)

def relocate_link(match):
    label, target = match.group(1), match.group(2)
    unwrapped = target[1:-1] if target.startswith('<') and target.endswith('>') else target
    if unwrapped.startswith(('https:', 'http:', '/')):
        return match.group(0)
    if target.startswith('../'):
        target = target[3:]
    else:
        target = 'audit/' + target
    return '[' + label + '](' + target + ')'

(destination / 'prize-report.md').write_text(
    re.sub(r'\[([^\]]*)\]\(([^)]*)\)', relocate_link, report))

summary = json.loads((project / 'logs/verification-summary.json').read_text())
assert all(v['exit_code'] == 0 for v in summary['checks'].values())
checks = destination / 'project-checks'
checks.mkdir(exist_ok=True)
for label in summary['checks']:
    for source in (project / 'logs').glob(label + '.*'):
        if source.is_file():
            shutil.copy2(source, checks / source.name)
for name in ('verification-summary.json', 'source-integrity-data.json'):
    shutil.copy2(project / 'logs' / name, checks / name)

argv = ['git', '-C', str(run / 'sources/proof'), 'bundle', 'create',
        str(destination / 'proof-snapshot.bundle'), 'HEAD']
result = subprocess.run(argv, capture_output=True, text=True)
(destination / 'bundle-create.log').write_text(result.stdout + result.stderr)
assert result.returncode == 0
check_argv = ['git', '-C', str(run / 'sources/proof'), 'bundle', 'verify',
              str(destination / 'proof-snapshot.bundle')]
checked = subprocess.run(check_argv, capture_output=True, text=True)
(destination / 'bundle-verify.log').write_text(checked.stdout + checked.stderr)
assert checked.returncode == 0

(destination / 'README.md').write_text('''# Preserved verification evidence

The final verdict and four required judgments are in [prize-report.md](prize-report.md).
The audit ran outside the original project in `/private/tmp/mm-lean-verify-20261010`.
This directory preserves its actual auditor inputs, original logs, proof exports,
workflow source, and evidence. Original absolute paths and commands in the records
describe the executed run; they were not rewritten to suggest a different execution.

`proof-snapshot.bundle` preserves the exact temporary local Git audit commit
`8b731b51dcb0ed3d7e8c6463b6266c35d8099c85`. It contains 53 unchanged original
source/config/script files and a snapshot-specific `.gitignore`. It contains no
generated proof objects. It is not a published or submitted repository revision.
The two trusted auditor Lean files are separate under `audit/`; the comparator's
private specification axiom is an expected-goal specification, never a solution
dependency. Production proofs use only the three standard Lean foundations.

`audit/exports/commands.json` records the actual exports, their raw SHA256 hashes,
and exact target names. Both raw NDJSON exports are retained. `workflow/` preserves
the requested skill at its pinned revision. `project-checks/` copies the actual
clean-build, direct source-check, axiom, kernel-replay and integrity records from
the original project's `logs/`.

For normal proof reproduction use the project's README, pinned toolchain and
manifest, then `sh scripts/verify.sh`. To reproduce the separate comparator audit,
restore the bundle in a separate local directory, install the two auditor Lean
files under `MaximumModulus/Audit/`, and regenerate exports with the recorded
commands. The stored native sandbox profile, runner, and target manifest contain
the original absolute run paths; adapt those auditor paths for a fresh run and
record that adaptation. Keep the production Lean files and dependency pins fixed.
The Linux-only comparator sandbox flag was disabled only inside the independently
enforced and probed macOS sandbox; see the report for the actual trust scope.
''')

hashes = {}
for path in sorted(destination.rglob('*')):
    if path.is_file() and path.name != 'archive-index.json':
        digest = hashlib.sha256()
        with path.open('rb') as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b''):
                digest.update(chunk)
        hashes[str(path.relative_to(destination))] = {
            'bytes': path.stat().st_size, 'sha256': digest.hexdigest()}
index = {'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'source_run': str(run), 'workflow_source': str(workflow),
         'destination': str(destination), 'bundle_create_argv': argv,
         'bundle_create_exit_code': result.returncode,
         'bundle_verify_argv': check_argv,
         'bundle_verify_exit_code': checked.returncode, 'files': hashes}
(destination / 'archive-index.json').write_text(json.dumps(index, indent=2) + '\n')
print(json.dumps({'files': len(hashes),
                  'bytes': sum(v['bytes'] for v in hashes.values()),
                  'destination': str(destination),
                  'bundle_verify_exit_code': checked.returncode}, indent=2))
