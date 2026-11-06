#!/usr/bin/env python3
"""Offline integrity checks for the public Aaron handoff; makes no API calls."""
import argparse
import csv
from collections import Counter
import hashlib
import json
from pathlib import Path


def validate(run):
    manifest=json.loads((run/'manifest.json').read_text())
    rows=list(csv.DictReader((run/'offline-checks.csv').open()))
    summaries=list(csv.DictReader((run/'model-summary.csv').open()))
    assert len(rows)==1260==len(manifest['calls'])
    assert len({(r['model'],r['problem'],r['sample']) for r in rows})==1260
    models={m['id'] for m in manifest['models'].values()}
    problems={f'p{i:02}' for i in range(1,11)}|{'p11a','p11b'}|{f'p{i:02}' for i in range(12,21)}
    assert set(r['model'] for r in rows)==models and len(models)==6
    assert Counter(r['model'] for r in rows)=={m:210 for m in models}
    assert all({(r['problem'],int(r['sample'])) for r in rows if r['model']==m}=={(p,n) for p in problems for n in range(10)} for m in models)
    samples=set()
    for row,call in zip(rows,manifest['calls']):
        assert row['cell_id']==call['cell_id']
        assert float(row['cost_usd'])==call['cost_usd']
        if row['sample_path']:
            path=run/row['sample_path'];samples.add(path)
            assert path.stat().st_size>0
            assert hashlib.sha256(path.read_bytes()).hexdigest()==row['sha256']==call['sha256']
        else:assert row['extracted_nonempty']=='False' and row['syntax_check_status']=='not_extracted'
    assert set(run.glob('*/p*/response*.yml'))==samples
    assert abs(sum(float(r['cost_usd']) for r in rows)-manifest['cost_accounted_usd'])<1e-8
    assert abs(sum(float(r['cost_usd']) for r in summaries)-manifest['cost_accounted_usd'])<1e-8
    assert manifest['cost_accounted_usd']<=25 and manifest['cost_by_provider']['anthropic']<=15
    raw=[json.loads(x) for x in (run/'raw-completions.jsonl').read_text().splitlines()]
    assert len(raw)==1260 and {x['cell_id'] for x in raw}=={r['cell_id'] for r in rows}
    for summary in summaries:
        subset=[r for r in rows if r['model']==summary['model']]
        for col in ['raw_nonempty','yaml_parses','extracted_nonempty','processed_yaml_parses','has_tasks','syntax_check_pass']:
            assert int(summary[col])==sum(r[col]=='True' for r in subset),(summary['model'],col)
        assert int(summary['forbidden_module_flags'])==sum(r['forbidden_module_flag']=='True' for r in subset)
        assert int(summary['syntax_check_fail'])==sum(r['syntax_check_pass']=='False' for r in subset)
    for call in manifest['calls']:
        task=next(t for t in manifest['tasks'] if t['task_id']==call['task_id'])
        prompt=manifest['prompt_template'].replace('{ task }',task['description'])
        assert hashlib.sha256(prompt.encode()).hexdigest()==call['prompt_sha256']
    return {'planned_rows':len(rows),'extracted_files':len(samples),'models':len(models),'problems':len(problems),'accounted_cost_usd':manifest['cost_accounted_usd'],'integrity':'pass'}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('run',type=Path);a=p.parse_args()
    print(json.dumps(validate(a.run),indent=2))
