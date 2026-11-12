#!/usr/bin/env python3
"""Offline dual-KB diagnostics. Never imports a provider transport or source corpus."""
import argparse
from collections import Counter,defaultdict
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from export_matrix import write_csv
from semantic_audit import probe

REPO=Path(__file__).resolve().parents[2]
BIN=REPO/'_build/default'
MODULES=sorted(str(p) for p in (REPO/'modules').glob('*.type'))

def sha(data):return hashlib.sha256(data).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def save(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')

def diagnose(text,kb):
    binary=BIN/('evaluation/native/effects_fallback.exe' if kb=='fallback' else 'evaluation/native/effects.exe')
    interp=BIN/('evaluation/native/query_interp_fallback.exe' if kb=='fallback' else 'bin/query_interp.exe')
    try:g=probe(text,binary)
    except (OSError,subprocess.TimeoutExpired) as e:g={'status':'driver_error','parsed':False,'semantic_accepted':False,'error':type(e).__name__}
    parsed=bool(g.get('parsed')) and g['status']!='empty_query'
    semantic=bool(g.get('semantic_accepted',g['status']=='ok'));native=None
    if semantic:
        with tempfile.TemporaryDirectory(prefix='kb-rescore-') as tmp:
            p=Path(tmp)/'query.fql';p.write_text(text)
            try:
                r=subprocess.run([str(interp),str(p),'--',*MODULES],text=True,capture_output=True,timeout=30)
                native={'returncode':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
            except subprocess.TimeoutExpired:native={'returncode':None,'error':'native_interpretation_timeout'}
    return {'probe':g,'parsed':parsed,'semantic_accepted':semantic,'interpreted':semantic and native['returncode']==0,'native':native}

def reason(d):
    if not d['parsed']:return 'empty query' if d['probe']['status']=='empty_query' else 'non-parsing output'
    if d['semantic_accepted']:return 'accepted'
    err=d['probe'].get('error','unknown semantic error')
    # Collapse varying object names only when the compiler uses a colon delimiter.
    return err.split(':',1)[0]

def rescore(run,out,workers=16):
    source=load(run/'per-cell.json');cache=out/'private/cache';cache.mkdir(parents=True,exist_ok=True)
    texts={r['output_sha256']:(run/r['output_path']).read_text() for r in source if r.get('output_path')}
    for digest,text in texts.items():assert sha(text.encode())==digest
    def check(item):
        digest,text=item
        for kb in ['example','fallback']:
            p=cache/f'{kb}-{digest}.json'
            if not p.exists():save(p,diagnose(text,kb))
    with ThreadPoolExecutor(max_workers=workers) as pool:list(pool.map(check,texts.items()))
    rows=[];original_reproduced=True
    for r in source:
        for kb in ['example','fallback']:
            d=load(cache/f"{kb}-{r['output_sha256']}.json") if r.get('output_path') else None
            if kb=='example' and d:
                original_reproduced &= all(r[k]==d[k] for k in ['parsed','semantic_accepted','interpreted'])
            rows.append({**{k:r.get(k) for k in ['cell_id','task_id','row_index','input_sha256','model','variant','status','output_sha256','output_path']},'kb':kb,
                'response':d is not None,'parsed':d['parsed'] if d else None,'semantic_accepted':d['semantic_accepted'] if d else None,
                'interpreted':d['interpreted'] if d else None,'rejection_reason':reason(d) if d else 'API-failed/pending',
                'semantic_error':d['probe'].get('error','') if d else '',
                'native_returncode':(d.get('native') or {}).get('returncode') if d else None})
    summary=[];reasons=[]
    for model in sorted({r['model'] for r in rows}):
        for kb in ['example','fallback']:
            rs=[r for r in rows if r['model']==model and r['kb']==kb]
            summary.append({'model':model,'kb':kb,'n':len(rs),'responses':sum(r['response'] for r in rs),
                'parsed':sum(r['parsed'] is True for r in rs),'semantic_accepted':sum(r['semantic_accepted'] is True for r in rs),
                'interpreted':sum(r['interpreted'] is True for r in rs),'unavailable':sum(not r['response'] for r in rs)})
            for why,n in Counter(r['rejection_reason'] for r in rs if r['response'] and not r['semantic_accepted']).most_common():
                reasons.append({'model':model,'kb':kb,'reason':why,'count':n})
    cross=[]
    for kb in ['example','fallback']:
        tasks=defaultdict(list)
        for r in rows:
            if r['kb']==kb:tasks[r['task_id']].append(r)
        cross.append({'kb':kb,'descriptions':len(tasks),'at_least_one_semantically_valid':sum(any(r['semantic_accepted'] is True for r in rs) for rs in tasks.values()),
            'all_responding_models_semantically_valid':sum(bool([r for r in rs if r['response']]) and all(r['semantic_accepted'] is True for r in rs if r['response']) for rs in tasks.values()),
            'all_six_responded_and_semantically_valid':sum(len(rs)==6 and all(r['response'] and r['semantic_accepted'] is True for r in rs) for rs in tasks.values())})
    out.mkdir(parents=True,exist_ok=True)
    for name,rs in [('per-cell.csv',rows),('model-summary.csv',summary),('rejection-reasons.csv',reasons),('cross-model.csv',cross)]:write_csv(out/name,rs)
    save(out/'per-cell.json',rows)
    source_paths=['evaluation/native/fallback_kb.ml','evaluation/native/effects.ml','evaluation/native/effects_fallback.ml','evaluation/native/query_interp_fallback.ml','bin/query_interp.ml','lib/fql/knowledge.ml','lib/fql/semant.ml','evaluation/code/kb_rescore.py']
    evidence={'paid_calls':0,'cost_usd':0,'source_run':str(run),'source_cells_sha256':sha((run/'per-cell.json').read_bytes()),'original_example_cell_flags_reproduced':original_reproduced,
        'parse_flags_identical':all(rs[0]['parsed']==rs[1]['parsed'] for rs in (rows[i:i+2] for i in range(0,len(rows),2))),
        'source_hashes':{p:sha((REPO/p).read_bytes()) for p in source_paths},'summary':summary,'cross_model':cross}
    save(out/'validation.json',evidence)
    assert evidence['parse_flags_identical']
    assert original_reproduced,'Existing Example flags changed; investigate before publication'
    print(json.dumps(evidence,indent=2),flush=True)
    return evidence


def benchmark(run,out,workers=16):
    refs={r['id']:r for r in load(REPO/'evaluation/datasets/references-private.json')}
    old=load(run/'per-call.json');manifest=load(run/'manifest.json');texts={}
    cells={c['id']:c for c in manifest['cells']}
    for ident,c in cells.items():
        p=run/'responses'/(ident+'.json')
        if p.exists():
            r=load(p)
            if r.get('text'):texts[sha(r['text'].encode())]=r['text']
    texts.update({sha(r['formal_query'].encode()):r['formal_query'] for r in refs.values()})
    cache=out/'private/benchmark-cache';cache.mkdir(parents=True,exist_ok=True)
    def check(item):
        h,text=item
        for kb in ['example','fallback']:
            p=cache/f'{kb}-{h}.json'
            if not p.exists():save(p,probe(text,BIN/f'evaluation/native/effects{"_fallback" if kb=="fallback" else ""}.exe'))
    with ThreadPoolExecutor(max_workers=workers) as pool:list(pool.map(check,texts.items()))
    def get(text,kb):return load(cache/f'{kb}-{sha(text.encode())}.json')
    refrows=[]
    for tid,r in refs.items():
        a,b=get(r['formal_query'],'example'),get(r['formal_query'],'fallback')
        refrows.append({'task_id':tid,'example_semantic':a['status']=='ok','fallback_semantic':b['status']=='ok','same_effects':a.get('effects')==b.get('effects')})
    rows=[]
    for ident,c in cells.items():
        model=manifest['config']['models'][c['model']]['id'];p=run/'responses'/(ident+'.json');r=load(p) if p.exists() else {};text=r.get('text','')
        row={'cell_id':ident,'model':model,'variant':c['variant'],'task_id':c['task_id'],'repeat':c['repeat'],'status':r.get('status','pending')}
        for kb in ['example','fallback']:
            g=get(text,kb) if text else {};gold=get(refs[c['task_id']]['formal_query'],kb)
            # Match the historical exporter exactly: serializer status ok is semantic acceptance here.
            row[kb+'_semantic']=g.get('status')=='ok' if text or r.get('status') in ('completed','incomplete') else None
            row[kb+'_ref_match']=g.get('status')==gold.get('status')=='ok' and g.get('effects')==gold.get('effects') if text or r.get('status') in ('completed','incomplete') else None
        rows.append(row)
    summary=[]
    for model,variant in sorted({(r['model'],r['variant']) for r in rows}):
        rs=[r for r in rows if r['model']==model and r['variant']==variant];prior=[r for r in old if r['model']==model and r['variant']==variant]
        summary.append({'model':model,'variant':variant,'n':len(rs),'published_example_semantic':sum(r['semantic_accepted'] is True for r in prior),
            'recomputed_example_semantic':sum(r['example_semantic'] is True for r in rs),'fallback_semantic':sum(r['fallback_semantic'] is True for r in rs),
            'published_example_ref_match':sum(r['ref_match'] is True for r in prior),'recomputed_example_ref_match':sum(r['example_ref_match'] is True for r in rs),
            'fallback_ref_match':sum(r['fallback_ref_match'] is True for r in rs)})
    for n,rs in [('benchmark-references.csv',refrows),('benchmark-per-cell.csv',rows),('benchmark-summary.csv',summary)]:write_csv(out/n,rs)
    report={'references':len(refrows),'all_references_unchanged':all(r['same_effects'] and r['example_semantic']==r['fallback_semantic'] for r in refrows),
        'all_cell_semantic_flags_unchanged':all(r['example_semantic']==r['fallback_semantic'] for r in rows),
        'all_cell_effect_match_flags_unchanged':all(r['example_ref_match']==r['fallback_ref_match'] for r in rows),
        'published_counts_reproduced':all(r['published_example_semantic']==r['recomputed_example_semantic'] and r['published_example_ref_match']==r['recomputed_example_ref_match'] for r in summary),
        'summary':summary,'paid_calls':0,'cost_usd':0}
    save(out/'benchmark-validation.json',report);print(json.dumps(report,indent=2),flush=True)
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--workers',type=int,default=16);p.add_argument('--benchmark',type=Path)
    a=p.parse_args();rescore(a.run,a.out,a.workers)
    if a.benchmark:benchmark(a.benchmark,a.out,a.workers)
