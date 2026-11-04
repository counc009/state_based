#!/usr/bin/env python3
"""Symbolic reference-program diagnostics; never executes Ansible or shell playbooks."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import tempfile
from evaluate import REPO, digest, load


def verify(query, playbook, binary):
    with tempfile.TemporaryDirectory() as tmp:
        q=Path(tmp)/'query.fql'; q.write_text(query)
        p=Path(tmp)/'program.yml'; p.write_text(playbook)
        modules=sorted(str(m) for m in (REPO/'modules').glob('*.type'))
        result=subprocess.run([str(binary),str(q),str(p),'--',*modules],
                              capture_output=True,text=True,timeout=60)
    statuses={0:'accepted_with_possible_assumptions_or_residuals',1:'module_parse_error',
              2:'module_lowering_error',3:'query_lowering_error',4:'program_lowering_error',
              5:'rejected',6:'trivial_query',7:'heuristics_rejected'}
    return {'status':statuses.get(result.returncode,'driver_error'),'returncode':result.returncode,
            'stdout':result.stdout,'stderr':result.stderr,
            'query_sha256':digest(query.encode()),'program_sha256':digest(playbook.encode())}


def audit(run,references,binary):
    refs={r['id']:r for r in load(references)}
    manifest=load(run/'manifest.json')
    control_rows=[]
    for ident,r in refs.items():
        control_rows.append({'task_id':ident,**verify(r['formal_query'],r['reference_solution'],binary)})
    rows=[]
    for cell in manifest['cells']:
        path=run/'responses'/(cell['id']+'.json')
        if not path.exists():
            rows.append({'cell':cell['id'],'status':'missing'});continue
        response=load(path)
        if response['status']!='completed':
            rows.append({'cell':cell['id'],'status':response['status']});continue
        ref=refs[cell['task_id']]
        assert cell['messages'][-1]['content']==ref['natural_language']
        row={'cell':cell['id'],'task_id':cell['task_id'],'variant':cell['variant'],
             'reference_program':verify(response['text'],ref['reference_solution'],binary)}
        # One explicitly diagnostic, post-hoc witness for the completed a01 smoke.
        if cell['task_id']=='a01':
            wrong=ref['reference_solution'].replace('/srv/www','/validation/wrong-target')
            assert wrong!=ref['reference_solution']
            row['wrong_path_program']=verify(response['text'],wrong,binary)
        rows.append(row)
    diagnostic_variants=[]
    if 'a20' in refs:
        ref=refs['a20']
        changed=ref['reference_solution'].replace('%wheel        ALL', '%wheel\\tALL')
        assert changed != ref['reference_solution'], 'Reference format changed; review diagnostic'
        diagnostic_variants.append({'task_id':'a20','change':'Only eight-space sudoers separator replaced with YAML-escaped tab; diagnostic, original untouched',
                                    **verify(ref['formal_query'],changed,binary)})
    return {'diagnostic_reference_variants':diagnostic_variants, 'references_sha256':digest(Path(references).read_bytes()),
            'binary_sha256':digest(binary.read_bytes()),
            'module_sha256':{str(p.relative_to(REPO)):digest(p.read_bytes()) for p in sorted((REPO/'modules').glob('*.type'))},
            'reference_controls':control_rows,'reference_control_statuses':dict(Counter(r['status'] for r in control_rows)),
            'cells':rows,
            'limits':'Supplied reference programs and FQL are controls, not independently reviewed gold. Symbolic acceptance may depend on initial-state assumptions and extra effects. No candidate playbook is executed. One wrong-path witness cannot prove adequacy for all obligations.'}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run',type=Path,required=True)
    p.add_argument('--references',type=Path,required=True)
    p.add_argument('--binary',type=Path,default=REPO/'_build/default/bin/verify.exe')
    a=p.parse_args()
    print(json.dumps(audit(a.run,a.references,a.binary),indent=2))
