import datetime, hashlib, json, pathlib, subprocess
run=pathlib.Path('/private/tmp/mm-lean-published-20261011')
root=run/'sources/site/proofs/maximum-modulus/lean'
repo=run/'sources/site'
selected=json.loads((run/'evidence/public-input.json').read_text())['selected_commit']
old=json.loads((run/'evidence/previous-source-snapshot.json').read_text())
expected={p:h for p,h in old['source_sha256'].items() if p!='.gitignore'}
assert len(expected)==53
def command(args):
    p=subprocess.run(['/usr/bin/git',*args],cwd=repo,capture_output=True,text=True)
    return {'argv':['/usr/bin/git',*args],'cwd':str(repo),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
head=command(['rev-parse','HEAD'])
assert head['exit_code']==0 and head['stdout'].strip()==selected
prefix='proofs/maximum-modulus/lean/'
files=[]
for rel,want in sorted(expected.items()):
    path=root/rel
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual==want,(rel,want,actual)
    blob=subprocess.run(['/usr/bin/git','show',selected+':'+prefix+rel],cwd=repo,capture_output=True)
    assert blob.returncode==0 and blob.stdout==path.read_bytes(),rel
    files.append({'path':rel,'sha256':actual,'verified_snapshot_sha256':want,'public_commit_blob_matches_worktree':True})
expected_modules=sorted(p for p in expected if p.startswith('MaximumModulus/') and p.endswith('.lean'))
actual_modules=sorted(str(p.relative_to(root)) for p in (root/'MaximumModulus').glob('*.lean'))
assert actual_modules==expected_modules
manuscript=root.parent/'maximum_modulus_points.tex'
manuscript_sha=hashlib.sha256(manuscript.read_bytes()).hexdigest()
assert manuscript_sha=='bc951c3ffa7d3579b2f39a0949e38db27338ac32ac050e3f5359d4452573a7b1'
tracked=command(['ls-files','--',prefix])
precompiled=[p for p in tracked['stdout'].splitlines() if pathlib.Path(p).suffix in {'.olean','.ilean','.so','.dylib'}]
assert not precompiled,precompiled
state=command(['status','--porcelain=v1','--untracked-files=all'])
tracked_changes=[s for s in state['stdout'].splitlines() if not s.startswith('??')]
assert not tracked_changes,tracked_changes
record={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'selected_public_commit':selected,
        'repository':'https://github.com/liyunpeng1991/liyunpeng1991.github.io','project_subdirectory':prefix.rstrip('/'),
        'source_scope':'All 53 production proof/config/script files; prior snapshot .gitignore deliberately excluded; no synthetic commit',
        'production_files':files,'count':len(files),'all_match_prior_verified_snapshot':True,
        'production_module_count':len(actual_modules),'head_command':head,'status_command':state,
        'tracked_source_list_command':tracked,'tracked_precompiled_project_artifacts':precompiled,
        'preserved_original_manuscript_sha256':manuscript_sha,
        'public_project_gitignore_sha256':hashlib.sha256((root/'.gitignore').read_bytes()).hexdigest()}
(run/'evidence/public-source-check.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in {'production_files','tracked_source_list_command','head_command','status_command'}},indent=2))
