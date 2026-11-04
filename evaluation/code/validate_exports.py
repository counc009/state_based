#!/usr/bin/env python3
"""Read-only consistency checks on public matrix exports; no API access."""
import argparse
from collections import Counter
import csv
import json
from pathlib import Path
import math


def validate(run):
    rows=json.loads((run/'per-call.json').read_text())
    csvrows=list(csv.DictReader((run/'per-call.csv').open()))
    attempts=json.loads((run/'per-attempt.json').read_text())
    assert len({(r['model'],r['variant'],r['task_id'],r['repeat'],r['attempt']) for r in attempts})==len(attempts)
    summaries=list(csv.DictReader((run/'model-variant-summary.csv').open()))
    tasks=list(csv.DictReader((run/'task-model-variant.csv').open()))
    meta=json.loads((run/'metadata.json').read_text())
    assert max(r['attempt'] for r in attempts)<=4
    assert all(v<=1 for v in Counter((r['model'],r['variant'],r['task_id'],r['repeat']) for r in attempts if r['status']=='completed').values())
    assert len(list(csv.DictReader((run/'per-attempt.csv').open())))==len(attempts)
    assert len(rows)==len(csvrows)==2520
    keys=[(r['model'],r['variant'],r['task_id'],r['repeat']) for r in rows]
    assert len(set(keys))==2520,'Duplicate/missing scientific cell'
    assert len({r['model'] for r in rows})==6
    assert {r['variant'] for r in rows}=={'compact-v1','handbook-v3'}
    assert len(summaries)==12 and len(tasks)==252
    assert all(n==10 for n in Counter(k[:3] for k in keys).values())
    assert all(n==210 for n in Counter(k[:2] for k in keys).values())
    assert all(r['reference_discrepancy']==(r['task_id'] in ('a03','a20')) for r in rows)
    assert all(r['ref_match'] is not True or (r['parsed'] is True and r['semantic_accepted'] is True) for r in rows)
    for summary in summaries:
        group=[r for r in rows if r['model']==summary['model'] and r['variant']==summary['variant']]
        correct=sum(r['ref_match'] is True for r in group)
        assert int(summary['n'])==len(group) and int(summary['correct'])==correct
        assert math.isclose(float(summary['rate']),correct/len(group))
        assert math.isclose(float(summary['cost_usd']),sum(r['cost_usd'] for r in group),abs_tol=1e-9)
    assert math.isclose(sum(r['cost_usd'] for r in attempts),sum(r['cost_usd'] for r in rows),abs_tol=1e-9)
    assert math.isclose(meta['matrix_cost_usd'],sum(r['cost_usd'] for r in rows),abs_tol=1e-9)
    assert meta['budget_accounted_usd']<=110+1e-6
    assert meta['anthropic_remaining']['already_accounted_usd']<=22+1e-6
    paper=list(csv.DictReader((run/'paper-baseline.csv').open()))
    assert len(paper)==11 and sum(int(r['correct']) for r in paper)==746
    assert sum(int(r['n']) for r in paper)==2310
    print(json.dumps({'validated_cells':len(rows),'model_variant_groups':len(summaries),'task_groups':len(tasks),
                      'statuses':dict(Counter(r['status'] for r in rows)),
                      'primary_correct':sum(r['ref_match'] is True for r in rows),
                      'accounted_usd':meta['budget_accounted_usd']},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('run',type=Path);a=p.parse_args();validate(a.run)
