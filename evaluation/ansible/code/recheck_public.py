#!/usr/bin/env python3
"""Replay extraction and optional free syntax checks from public artifacts alone."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import tempfile
from check_and_package import extract,parse_yaml,forbidden,syntax_check,REPO
from validate_export import validate


def recheck(run,syntax=False,workers=6):
    validate(run)
    manifest=json.loads((run/'manifest.json').read_text())
    calls={r['cell_id']:r for r in manifest['calls']}
    raw=[json.loads(line) for line in (run/'raw-completions.jsonl').read_text().splitlines()]
    checked=[]
    with tempfile.TemporaryDirectory(prefix='astrogator-public-replay-') as tmp:
        stage=Path(tmp)
        for answer in raw:
            row=calls[answer['cell_id']];text=extract(answer['text']);ok,doc,_=parse_yaml(text) if text.strip() else (False,None,'')
            assert ok==row['yaml_parses'],row['cell_id']
            if answer['text'].strip():
                p=stage/row['model']/row['problem']/f'raw{row["sample"]}.yml';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
        proc=REPO/'_build/default/evaluation/ansible/native/paper_process.exe'
        subprocess.run([str(proc),*[m['id'] for m in manifest['models'].values()]],cwd=stage,check=True,capture_output=True,text=True)
        for row in calls.values():
            rel=Path(row['model'])/row['problem']/f'response{row["sample"]}.yml'
            recreated=stage/rel
            assert recreated.exists()==bool(row['sample_path']),row['cell_id']
            if recreated.exists():
                assert recreated.read_bytes()==(run/rel).read_bytes(),row['cell_id']
                ok,doc,_=parse_yaml(recreated.read_text());assert ok==row['processed_yaml_parses']
                assert set(forbidden(doc))<=set(row['forbidden_modules'].split(','))
                checked.append((row,recreated))
        if syntax:
            def check(item):
                row,path=item;result=syntax_check(path)
                assert result['syntax_check_status']==row['syntax_check_status'],row['cell_id']
            with ThreadPoolExecutor(max_workers=workers) as pool:list(pool.map(check,checked))
    return {'planned':len(calls),'extracted_files_reproduced':len(checked),'syntax_rechecked':syntax,'result':'pass'}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('run',type=Path);p.add_argument('--syntax',action='store_true');p.add_argument('--workers',type=int,default=6);a=p.parse_args()
    print(json.dumps(recheck(a.run,a.syntax,a.workers),indent=2))
