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
    call_map={r['cell_id']:r for r in manifest['calls']}
    for answer in raw:assert hashlib.sha256(answer['text'].encode()).hexdigest()==call_map[answer['cell_id']]['raw_text_sha256']
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
    report={'planned_rows':len(rows),'extracted_files':len(samples),'models':len(models),'problems':len(problems),'accounted_cost_usd':manifest['cost_accounted_usd'],'integrity':'pass'}
    if 'refresh' in manifest:
        original=json.loads((run/'history/cap-4096/manifest.json').read_text())
        old={r['cell_id']:r for r in original['calls']};current={r['cell_id']:r for r in manifest['calls']}
        selected=set(manifest['refresh']['selected_cell_ids'])
        assert hashlib.sha256((run/'history/cap-4096/manifest.json').read_bytes()).hexdigest()==manifest['refresh']['base_public_manifest_sha256']
        assert len(selected)==133 and selected=={k for k,r in old.items() if r['status']=='incomplete'}
        assert all(old[k]['stop_reason']=='length' and old[k]['output_tokens']==4096 for k in selected)
        for key in selected:
            if old[key]['sample_path']:
                archived=run/'history/cap-4096/selected-old-samples'/old[key]['sample_path']
                assert hashlib.sha256(archived.read_bytes()).hexdigest()==old[key]['sha256']
        for key,row in old.items():
            if key in selected:continue
            assert all(current[key][field]==row[field] for field in ['status','raw_text_sha256','sample_path','sha256','cost_usd','attempts'])
        history=list(csv.DictReader((run/'attempt-history.csv').open()))
        answers=[json.loads(line) for line in (run/'attempt-history.jsonl').read_text().splitlines()]
        assert len(history)==len(answers)==len(manifest['attempts'])
        assert len({(r['cell_id'],r['attempt']) for r in history})==len(history)
        new=[a for a in manifest['attempts'] if a['phase']=='cap-refresh-32768']
        assert {a['cell_id'] for a in new}<=selected
        assert sum(a['phase']=='initial-4096' for a in manifest['attempts'])==1260
        initial={(a['cell_id'],a['attempt']):a for a in original['attempts']}
        for a in manifest['attempts']:
            if a['phase']=='initial-4096':assert all(a[k]==v for k,v in initial[a['cell_id'],a['attempt']].items())
        for answer in answers:assert hashlib.sha256(answer['text'].encode()).hexdigest()==answer['raw_text_sha256']
        assert abs(sum(float(r['cost_usd']) for r in history)-manifest['cost_accounted_usd'])<1e-8
        extra=sum(a['cost_usd'] for a in new)
        assert extra<=5 and abs(extra-manifest['refresh']['additional_cost_accounted_usd'])<1e-8
        assert abs(original['cost_accounted_usd']+extra-manifest['cost_accounted_usd'])<1e-8
        for a in new:
            row=current[a['cell_id']];model=manifest['models'][row['model_key']]
            task=next(t for t in manifest['tasks'] if t['task_id']==row['task_id'])
            body={'model':row['model'],'messages':[{'role':'user','content':manifest['prompt_template'].replace('{ task }',task['description'])}],
                'max_tokens':32768,'reasoning_effort':model['reasoning_effort'],'stream':True,'stream_options':{'include_usage':True}}
            assert hashlib.sha256(json.dumps(body,sort_keys=True).encode()).hexdigest()==a['request_sha256']
            assert a['max_output_tokens']==32768
        report['cap_refresh']={'selected':len(selected),'original_completed_cells_preserved':len(old)-len(selected),
            'additional_attempts':len(new),'additional_cost_usd':extra,'still_at_cap':sum(r['still_at_cap'] for r in current.values()),
            'request_body_hashes_verified':True}
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('run',type=Path);a=p.parse_args()
    print(json.dumps(validate(a.run),indent=2))
