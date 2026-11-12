#!/usr/bin/env python3
"""Rerun only the original 4,096-token length-limited cells, with a separate $5 ledger."""
import argparse
import copy
from datetime import datetime,timezone
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
from generate import REPO,Matrix,build,request
import evaluate as ev

EXPECTED={'qwen3.8-flash':95,'deepseek-v4.1-flash':21,'deepseek-v4-flash':17}


def freeze(run,catalog):
    old=ev.load(run/'private/manifest.json');public=ev.load(run/'manifest.json')
    selected=[r for r in public['calls'] if r['status']=='incomplete']
    assert len(selected)==133
    assert {k:sum(r['model']==k for r in selected) for k in EXPECTED}==EXPECTED
    assert all(r['stop_reason']=='length' and r['output_tokens']==4096 and r['attempts']==1 for r in selected)
    history=run/'history/cap-4096';history.mkdir(parents=True,exist_ok=True)
    for name in ['manifest.json','offline-checks.csv','model-summary.csv','raw-completions.jsonl','validation.json','README.md','task-map.csv']:
        src=run/name;dst=history/name
        if dst.exists():assert dst.read_bytes()==src.read_bytes(),'Existing history differs; use the frozen refresh manifest to resume'
        else:shutil.copyfile(src,dst)
    for row in selected:
        if row['sample_path']:
            dest=history/'selected-old-samples'/row['sample_path'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(run/row['sample_path'],dest)
    history.joinpath('PROVENANCE.md').write_text('Original 4,096-token run, preserved before the authorized cap-only rerun. Source commit: '+subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()+'.\n\nThe original CSV/manifest paths refer to the run root at that commit. Completed sample files stay unchanged in the canonical model directories; original extracted files for the 133 selected cells are also copied under selected-old-samples/. All original raw answers and token/cost records are retained here.\n')
    manifest=copy.deepcopy(old);ids={r['cell_id'] for r in selected};manifest['cells']=[c for c in old['cells'] if c['id'] in ids]
    manifest['config'].update(max_output_tokens=32768,total_budget_usd=5,prior_cost_usd=0,prior_anthropic_cost_usd=0,stream_deadline_s=3600)
    manifest['config']['matrix_status']='Darsh approved only 133 original length-limited cells, 32768 tokens, $5 extra; completed cells excluded'
    manifest['created_at']=datetime.now(timezone.utc).isoformat()
    caps={key:min(32768,catalog[key]['limit']['output']) for key in EXPECTED}
    assert set(caps.values())=={32768},'A lower provider cap requires a per-model request cap'
    manifest['refresh']={'reason':'Original 133 incomplete samples all ended at the operator-imposed 4096-token cap; cap constraint, not model failure',
        'selected_cell_ids':sorted(ids),'selected_counts':EXPECTED,'old_max_output_tokens':4096,'new_max_output_tokens_by_model':caps,
        'extra_budget_usd':5,'base_accounted_usd':public['cost_accounted_usd'],'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip(),
        'base_public_manifest_sha256':ev.digest((run/'manifest.json').read_bytes()),'base_private_manifest_sha256':ev.digest(old),
        'catalog_source':'https://api.router.agentfan.club/api/models','catalog_checked_at':manifest['created_at'],
        'catalog_output_limits':{key:catalog[key]['limit']['output'] for key in EXPECTED},'catalog_sha256':ev.digest(catalog),
        'sources':{'generator_sha256':ev.digest((REPO/'evaluation/ansible/code/generate.py').read_bytes()),'refresh_runner_sha256':ev.digest(Path(__file__).read_bytes())},
        'sampling':'Original single-user prompt and reasoning setting unchanged; no seed/temperature/top-p supplied; independent fresh completion replaces the selected canonical sample'}
    return manifest


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('command',choices=['freeze','run']);p.add_argument('--run',type=Path,required=True);p.add_argument('--catalog',type=Path);p.add_argument('--credentials-file',type=Path);p.add_argument('--workers',type=int,default=24);a=p.parse_args()
    output=a.run/'private/cap-32768';output.mkdir(parents=True,exist_ok=True)
    if a.command=='freeze':
        assert a.catalog and not (output/'manifest.json').exists()
        m=freeze(a.run,ev.load(a.catalog));ev.write_new(output/'manifest.json',m);print(json.dumps(ev.estimate(m),indent=2));return
    assert a.credentials_file and a.workers>0
    os.environ.update({k:v for k,v in ev.load(a.credentials_file).items() if k in {'OPENAI_API_KEY','ANTHROPIC_API_KEY','AGENTFANCLUB_API_KEY','AGENTFANCLUB_BASE_URL'}})
    with (output/'.matrix.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);m=ev.load(output/'manifest.json')
        assert len(m['cells'])==133 and all(c['model'] in EXPECTED for c in m['cells'])
        assert m['config']['max_output_tokens']==32768
        Matrix(m,output,5,0,4,request,build).run(a.workers)

if __name__=='__main__':main()
