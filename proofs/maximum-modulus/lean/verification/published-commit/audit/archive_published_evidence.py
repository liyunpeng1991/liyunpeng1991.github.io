#!/usr/bin/env python3
"""Archive completed fresh local evidence; performs no remote action."""
import datetime, gzip, hashlib, json, pathlib, shutil, subprocess, tarfile
run=pathlib.Path('/private/tmp/mm-lean-published-20261011')
dest=pathlib.Path('/Users/gluon/Documents/ChatGPT/Maximum Modulus/publication/v2/verification-published')
root=run/'sources/site'
project=root/'proofs/maximum-modulus/lean'
assert (run/'report.md').is_file()
for label in ['project-clean-verification','workflow-target-run','comparator-exports','comparator-paranoid']:
    assert json.loads((run/'logs'/(label+'.json')).read_text())['exit_code']==0,label
dest.mkdir(parents=True,exist_ok=True)
curated=dest/'published-commit'
curated.mkdir(exist_ok=True)
assert not (dest/'archive-index.json').exists(),'Do not overwrite completed archive'
for name in ['evidence','logs']:
    shutil.copytree(run/name,curated/name,dirs_exist_ok=True)
shutil.copytree(run/'audit',curated/'audit',dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('*.ndjson','__pycache__'))
shutil.copytree(project/'logs',curated/'project-logs',dirs_exist_ok=True)
shutil.copy2(run/'report.md',dest/'public-commit-report.md')
workflow=pathlib.Path('/private/tmp/mm-lean-verify-workflow-20261010')
shutil.copytree(workflow,curated/'pinned-workflow',dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('__pycache__'))
previous_setup=pathlib.Path('/private/tmp/mm-lean-verify-20261010/evidence/setup-logs')
if previous_setup.is_dir():
    shutil.copytree(previous_setup,curated/'historical-cache-tool-provenance',dirs_exist_ok=True)
exports=[]
(dest/'raw-exports').mkdir(exist_ok=True)
for label in ['challenge','solution']:
    raw=run/'audit/exports'/(label+'.ndjson')
    compressed=dest/'raw-exports'/(label+'.ndjson.gz')
    with raw.open('rb') as f, compressed.open('wb') as out:
        with gzip.GzipFile(fileobj=out,mode='wb',filename='',mtime=0,compresslevel=6) as g:
            shutil.copyfileobj(f,g)
    with raw.open('rb') as f: rawsha=hashlib.file_digest(f,'sha256').hexdigest()
    with gzip.open(compressed,'rb') as f: checksha=hashlib.file_digest(f,'sha256').hexdigest()
    assert rawsha==checksha,label
    exports.append({'label':label,'raw_bytes':raw.stat().st_size,'raw_sha256':rawsha,
                    'compressed_file':str(compressed.relative_to(dest)),
                    'compressed_bytes':compressed.stat().st_size,
                    'compressed_sha256':hashlib.file_digest(compressed.open('rb'),'sha256').hexdigest(),
                    'decompressed_sha256_rechecked':checksha})
tracked=subprocess.check_output(['/usr/bin/git','ls-files','--','proofs/maximum-modulus'],cwd=root,text=True).splitlines()
with tarfile.open(curated/'public-source-files.tar.gz','w:gz') as archive:
    for rel in tracked: archive.add(root/rel,arcname=rel,recursive=False)
source_sha=json.loads((run/'evidence/public-input.json').read_text())['selected_commit']
files={str(p.relative_to(dest)):{'bytes':p.stat().st_size,
       'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest()}
       for p in sorted(dest.rglob('*')) if p.is_file() and p.name!='archive-index.json'}
record={'archived_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'selected_public_source_commit':source_sha,'source':str(run),'destination':str(dest),
        'source_archive_scope':'Tracked public proofs/maximum-modulus distribution only; no generated cache/build products or auditor additions',
        'source_distribution_files':tracked,'exports':exports,'files':files,
        'remote_actions':False,'original_project_proof_or_manuscript_mutations':False}
(dest/'archive-index.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'source_commit':source_sha,'archive':str(dest),'files':len(files),'exports':exports},indent=2))
