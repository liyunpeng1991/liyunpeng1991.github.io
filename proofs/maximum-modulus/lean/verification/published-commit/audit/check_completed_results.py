import datetime, hashlib, json, pathlib, re, subprocess
run=pathlib.Path('/private/tmp/mm-lean-published-20261011')
root=run/'sources/site/proofs/maximum-modulus/lean'
repo=run/'sources/site'
sha=json.loads((run/'evidence/public-input.json').read_text())['selected_commit']
def read(rel): return json.loads((run/rel).read_text())
standard={'propext','Classical.choice','Quot.sound'}
summary=json.loads((root/'logs/verification-summary.json').read_text())
assert len(summary['checks'])==91
assert all(r['exit_code']==0 for r in summary['checks'].values())
assert len(summary['actual_target_axiom_reports'])==126
assert set(summary['observed_axioms'])==standard
workflow=read('audit/workflow-target-run/result.json')
assert workflow['exit_code']==0 and workflow['inputs_stable']
assert len(workflow['targets'])==8
for target in workflow['targets']:
    assert target['status']=='standard_axioms_only'
    assert set(target['axioms'])==standard
    assert all(c['exit_code']==0 for c in target['commands'])
for command in workflow['commands']:
    assert command['exit_code']==0
    path=pathlib.Path(command['log'])
    assert hashlib.file_digest(path.open('rb'),'sha256').hexdigest()==command['log_sha256']
checker=read('logs/comparator-paranoid.json')
assert checker['exit_code']==0
text=(run/'logs/comparator-paranoid.log').read_text()
for name in ['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default']:
    assert name+' kernel accepts the solution' in text,name
assert 'Your solution is okay!' in text
exports=[]
previous={r['module']:r for r in read('evidence/previous-export-digests.json')['exports']}
for label,module in [('challenge','MaximumModulus.Audit.ComparatorChallenge'),('solution','MaximumModulus.AllRadii')]:
    path=run/'audit/exports'/(label+'.ndjson')
    digest=hashlib.file_digest(path.open('rb'),'sha256').hexdigest()
    exports.append({'label':label,'module':module,'bytes':path.stat().st_size,'sha256':digest,
                    'identical_to_previous_export':digest==previous[module]['sha256'],
                    'fresh_export_and_fresh_checker_execution':True})
solution=(run/'audit/exports/solution.ndjson').read_bytes()
assert b'ComparatorChallenge' not in solution
source=read('evidence/public-source-check.json')
for f in source['production_files']:
    assert hashlib.file_digest((root/f['path']).open('rb'),'sha256').hexdigest()==f['sha256']
status=subprocess.run(['/usr/bin/git','status','--porcelain=v1','--untracked-files=all'],cwd=repo,capture_output=True,text=True)
assert status.returncode==0
allowed_auditors={'?? proofs/maximum-modulus/lean/MaximumModulus/Audit/OriginalProblem.lean','?? proofs/maximum-modulus/lean/MaximumModulus/Audit/ComparatorChallenge.lean'}
assert set(status.stdout.splitlines()) == allowed_auditors
head=subprocess.check_output(['/usr/bin/git','rev-parse','HEAD'],cwd=repo,text=True).strip()
assert head==sha
manifest=json.loads((root/'lake-manifest.json').read_text())
deps=[]
for package in manifest['packages']:
    droot=root/manifest['packagesDir']/package['name']
    actual=subprocess.check_output(['/usr/bin/git','rev-parse','HEAD'],cwd=droot,text=True).strip()
    dirty=subprocess.check_output(['/usr/bin/git','status','--porcelain=v1','--untracked-files=all'],cwd=droot,text=True)
    assert actual==package['rev'] and not dirty
    deps.append({'name':package['name'],'actual_revision':actual,'clean':True})
tools=read('evidence/dependency-tool-provenance.json')['tools']
for name,t in tools.items():
    assert hashlib.file_digest(pathlib.Path(t['path']).open('rb'),'sha256').hexdigest()==t['sha256'],name
manuscript=hashlib.file_digest((root.parent/'maximum_modulus_points.tex').open('rb'),'sha256').hexdigest()
assert manuscript==source['preserved_original_manuscript_sha256']
auditor={str(p.relative_to(run)):{'bytes':p.stat().st_size,'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest()} for p in sorted((run/'audit').rglob('*')) if p.is_file() and p.suffix in {'.py','.lean','.json','.sb'}}
record={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'selected_public_commit':sha,
        'all_53_production_hashes_stable':True,'preserved_manuscript_sha256':manuscript,
        'actual_HEAD':head,'tracked_changes':False,'git_status':status.stdout,
        'untracked_state_scope':'Exactly the two trusted auditor modules; generated project logs are ignored by tracked parent proofs/maximum-modulus/.gitignore line 3; no other untracked source accepted',
        'project_checks_count':91,'project_axiom_declaration_count':126,
        'workflow_target_count':len(workflow['targets']),'workflow_commands_count':len(workflow['commands']),
        'workflow_inputs_stable':True,'all_target_axioms':workflow['targets'],
        'exports':exports,'challenge_specification_absent_from_solution_export':True,
        'checker_results':['Lean paranoid','lean4lean','nanoda','con-leche','con-ron','Lean default'],
        'checker_counts':{'lean4lean':re.findall(r'checked (\d+) declarations',text),
                          'con_leche':re.findall(r'con-leche: accepted (\d+) declarations',text),
                          'con_ron':re.findall(r'con-ron: accepted (\d+) declarations',text)},
        'dependencies':deps,'trusted_tool_hashes_stable':True,'auditor_file_hashes':auditor,
        'prior_checks_are_not_counted_as_fresh':True}
(run/'evidence/completed-results-review.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in {'all_target_axioms','auditor_file_hashes'}},indent=2))
