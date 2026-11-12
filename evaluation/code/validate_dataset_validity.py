#!/usr/bin/env python3
"""Offline integrity/privacy checks for the published validity-only exports."""
import argparse
from collections import Counter
import csv
import json
import random
from pathlib import Path
import evaluate as ev
from matrix_run import usage_cost


def read_csv(path):
    with path.open() as stream:return list(csv.DictReader(stream))


def validate(run):
    manifest=ev.load(run/'manifest.json');rows=ev.load(run/'per-cell.json');sample=read_csv(run/'sample-ids.csv');filtered=read_csv(run/'filter-decisions.csv');attempts=read_csv(run/'per-attempt.csv')
    ids={r['task_id'] for r in sample};n=manifest['funnel']['sampled'];assert len(sample)==len(ids)==n<=300
    assert len(filtered)==manifest['funnel']['total'];assert len({r['task_id'] for r in filtered})==len(filtered)
    assert not ({'input','nl','output'} & set(sample[0]))
    assert not ({'input','nl','output'} & set(filtered[0]))
    prefix=manifest['funnel'].get('hash_prefix_batches')
    if prefix is not None:
        chosen=set(sorted({r['nl_sha256'] for r in filtered if r['heuristic_keep']=='True'})[:prefix*20])
        assert all((r['in_filter_subset']=='True')==(r['heuristic_keep']=='True' and r['nl_sha256'] in chosen) for r in filtered)
    kept=[r for r in filtered if r['in_filter_subset']=='True' and r['detail_keep']=='True']
    assert len(kept)==manifest['funnel']['after_detail_check']
    expected_sample=random.Random(manifest['funnel']['sample_seed']).sample(kept,min(300,len(kept)))
    assert [r['task_id'] for r in expected_sample]==[r['task_id'] for r in sample]
    models={m['id'] for m in manifest['models'].values()};assert len(models)==6 and len(rows)==6*n
    assert len({r['cell_id'] for r in rows})==len(rows)
    assert Counter(r['model'] for r in rows)=={model:n for model in models}
    for model in models:assert {r['task_id'] for r in rows if r['model']==model}==ids
    for r in rows:
        assert r['variant']=='handbook-v3' and r['repeat']==0 and r['max_output_tokens']==32768
        assert not r['semantic_accepted'] or r['parsed'] is True
        assert not r['interpreted'] or r['semantic_accepted'] is True
        if r['output_path']:
            output=run/r['output_path'];assert output.exists() and ev.digest(output.read_bytes())==r['output_sha256']
        if r['status']=='pending_budget':assert r['attempts']==0 or not r['output_path']
    for summary in manifest['summary']:
        rs=[r for r in rows if r['model']==summary['model']]
        for key in ['parsed','semantic_accepted','interpreted','api_failure']:
            dest='api_failures' if key=='api_failure' else key
            assert summary[dest]==sum(r[key] is True for r in rs)
        assert abs(summary['cost_usd']-sum(r['cost_usd'] for r in rs))<1e-8
    models_by_id={m['id']:m for m in manifest['models'].values()}
    for attempt in attempts:
        expected,_=usage_cost({'usage':json.loads(attempt['provider_usage_json'])},models_by_id[attempt['model']],float(attempt['reserved_usd']))
        assert abs(expected-float(attempt['cost_usd']))<1e-8
    cost=manifest['costs'];assert abs(sum(float(a['cost_usd']) for a in attempts)-cost['total_accounted_usd'])<1e-8
    assert cost['total_accounted_usd']<=20+1e-8 and cost['anthropic_usd']<=8+1e-8
    assert manifest['correctness_claim'] is False and manifest['reference_comparison'] is False and manifest['output_judge'] is False and manifest['runtime_execution'] is False
    private=run/'private'
    if private.exists():
        for phase in ['filter','generation']:
            m=ev.load(private/phase/'manifest.json');s=ev.load(private/phase/'state.json');assert s['manifest_sha256']==ev.digest(m)
            for attempt in s['attempts']:
                body=attempt['request_body'];assert not {'seed','temperature','top_p'} & set(body)
                cap=body.get('max_output_tokens',body.get('max_tokens'));assert cap==(4096 if phase=='filter' else 32768)
                if phase=='filter':
                    assert body['reasoning_effort']=='low'
                    inputs=json.loads(body['messages'][1]['content']);assert all(set(r)=={'id','nl'} for r in inputs)
        provider_keys=Path('/tmp/astrogator-provider-env.json')
        if provider_keys.exists():
            secrets=[value.encode() for key,value in ev.load(provider_keys).items() if key.endswith(('_KEY','_TOKEN')) and value]
            pat=Path('/tmp/astrogator-gh-token')
            if pat.exists():secrets.append(pat.read_bytes().strip())
            public=[p for p in run.rglob('*') if p.is_file() and 'private' not in p.relative_to(run).parts]
            assert not any(secret in p.read_bytes() for p in public for secret in secrets),'Secret detected in public artifact'
    print(json.dumps({'validated':True,'source_rows':len(filtered),'sampled':n,'cells':len(rows),'outputs':sum(bool(r['output_path']) for r in rows),'accounted_usd':cost['total_accounted_usd']}))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('run',type=Path);validate(p.parse_args().run)
