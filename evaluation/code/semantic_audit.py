#!/usr/bin/env python3
"""Post-generation reference and requirement diagnostics; never imports into inference."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import tempfile

from evaluate import REPO, digest, load


def probe(text, binary):
    with tempfile.TemporaryDirectory() as tmp:
        query = Path(tmp)/'query.fql'
        query.write_text(text)
        result = subprocess.run([str(binary), str(query)], capture_output=True, text=True, timeout=30)
    try:
        obj = json.loads(result.stdout)
    except ValueError:
        obj = {'status':'driver_error','stdout':result.stdout,'stderr':result.stderr}
    return {**obj, 'returncode':result.returncode}


def directory_obligations(natural_language, effects):
    """Independent narrow extraction from NL, not from the reference FQL or model outputs.

    Checks only an explicitly requested directory/path. Other task forms abstain.
    This is not a general NL-understanding or intent-correctness oracle.
    """
    match = re.fullmatch(r'Create directory (/[\w/.-]+)', natural_language.strip())
    if not match:
        return {'status':'unsupported'}
    target = match.group(1)
    actions = [e for e in effects if e.get('kind') == 'create_directory']
    found = any(e.get('destination',{}).get('path') ==
                {'kind':'remote','destination':{'kind':'absolute','value':target}} for e in actions)
    return {'status':'specified_obligation_present' if found else 'specified_obligation_missing',
            'required_remote_directory':target, 'action_count':len(effects),
            'extra_actions_require_review':len(effects) != 1}


def audit(run, references, binary, interpreter=None):
    refs = {b['id']:b for b in load(references)}
    manifest = load(run/'manifest.json')
    reference_probes = {key:probe(value['formal_query'],binary) for key,value in refs.items()}
    rows = []
    for cell in manifest['cells']:
        row = {'cell':cell['id'],'task_id':cell['task_id'],'variant':cell['variant'],
               'model':cell['model'],'repeat':cell['repeat']}
        path = run/'responses'/(cell['id']+'.json')
        if not path.exists():
            rows.append({**row,'status':'missing'}); continue
        response = load(path)
        if response['status'] != 'completed':
            rows.append({**row,'status':response['status']}); continue
        reference = refs[cell['task_id']]
        # Prevent accidentally scoring a different dataset revision as the same task.
        assert cell['messages'][-1]['content'] == reference['natural_language'], 'NL/reference mismatch'
        generated = probe(response['text'],binary)
        gold = reference_probes[cell['task_id']]
        row.update(status=generated['status'], generated=generated,
                   supplied_reference=gold, query_sha256=digest(response['text'].encode()))
        if generated['status'] == gold['status'] == 'ok':
            row['reference_effect_tree_match'] = generated['effects'] == gold['effects']
            row['nl_directory_obligations'] = directory_obligations(reference['natural_language'],generated['effects'])
        if interpreter:
            with tempfile.TemporaryDirectory() as tmp:
                query = Path(tmp)/'query.fql'; query.write_text(response['text'])
                modules = sorted(str(p) for p in (REPO/'modules').glob('*.type'))
                result = subprocess.run([str(interpreter),str(query),'--',*modules],capture_output=True,text=True,timeout=30)
                row['symbolic_interpretation'] = {'returncode':result.returncode,'stdout':result.stdout,'stderr':result.stderr}
        rows.append(row)
    groups = {}
    for key in sorted({(r['model'],r['variant']) for r in rows}):
        selected = [r for r in rows if (r['model'],r['variant']) == key]
        groups[' / '.join(key)] = {
            'planned':len(selected),'statuses':dict(Counter(r['status'] for r in selected)),
            'reference_effect_tree_matches':sum(r.get('reference_effect_tree_match',False) for r in selected),
            'nl_directory_obligation_present':sum(r.get('nl_directory_obligations',{}).get('status')=='specified_obligation_present' for r in selected),
            'symbolic_interpretation_pass':sum(r.get('symbolic_interpretation',{}).get('returncode') == 0 for r in selected)}
    return {'manifest_sha256':digest(manifest),'references_sha256':digest(Path(references).read_bytes()),
            'binary_sha256':digest(Path(binary).read_bytes()),'reference_statuses':dict(Counter(p['status'] for p in reference_probes.values())),
            'groups':groups,'cells':rows,
            'limits':'Effect-tree equality is a structural semantic proxy relative to supplied, not independently adjudicated, references. Narrow NL checks abstain outside explicit directory creation. Neither proves user intent or equivalence on all program behaviors.'}


def controls(binary):
    # Neutral paths; generated after the smoke as diagnostic validation, never prompt tuning.
    cases = [
        ('unquoted','create directory at /validation/out',True),
        ('quoted','create directory at "/validation/out"',True),
        ('wrong_path','create directory at /validation/other',False),
        ('wrong_operation','create file at /validation/out',False),
        ('omitted','create directory at /validation/unrelated',False)]
    rows=[]
    for name,query,expected in cases:
        p=probe(query,binary)
        result=directory_obligations('Create directory /validation/out',p.get('effects',[]))
        actual=result['status']=='specified_obligation_present'
        rows.append({'name':name,'query':query,'probe':p,'obligations':result,
                     'expected_obligation_present':expected,'control_pass':p['status']=='ok' and actual==expected})
    return rows


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run',type=Path,required=True)
    p.add_argument('--references',type=Path,required=True)
    p.add_argument('--binary',type=Path,default=REPO/'_build/default/evaluation/native/effects.exe')
    p.add_argument('--interpreter',type=Path)
    a=p.parse_args()
    report=audit(a.run,a.references,a.binary,a.interpreter)
    report['diagnostic_controls']=controls(a.binary)
    print(json.dumps(report,indent=2))
