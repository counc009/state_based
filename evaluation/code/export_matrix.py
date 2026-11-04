#!/usr/bin/env python3
"""Score all frozen cells, retaining failures/pending cells; export public tidy rows."""
import argparse
from collections import Counter,defaultdict
import csv
import json
import math
from pathlib import Path
import statistics
import subprocess
import tempfile
from evaluate import REPO,digest,load
from semantic_audit import probe,directory_obligations
from reference_verifier_audit import verify


def wilson(correct,n):
    if not n:return None,None
    z=1.959963984540054;p=correct/n;den=1+z*z/n
    mid=(p+z*z/(2*n))/den
    half=z*math.sqrt(p*(1-p)/n+z*z/(4*n*n))/den
    return mid-half,mid+half


def write_csv(path,rows):
    with path.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader();writer.writerows(rows)


def totals(records,provider):
    inp=out=reason=0;known=False;reason_known=False
    for rec in records:
        u=rec.get('usage')
        if not isinstance(u,dict):continue
        known=True
        inp+=u.get('input_tokens',u.get('prompt_tokens',0))
        if provider=='anthropic':inp+=u.get('cache_creation_input_tokens',0)+u.get('cache_read_input_tokens',0)
        out+=u.get('output_tokens',u.get('completion_tokens',0))
        details=u.get('output_tokens_details') or u.get('completion_tokens_details') or {}
        rt=u.get('reasoning_tokens',details.get('reasoning_tokens',details.get('thinking_tokens')))
        if rt is not None:reason+=rt;reason_known=True
    return (inp,out,reason if reason_known else None) if known else (None,None,None)


def summarize(rows,keys):
    groups=defaultdict(list)
    for row in rows:groups[tuple(row[k] for k in keys)].append(row)
    result=[]
    for key,rs in sorted(groups.items()):
        n=len(rs);correct=sum(r['ref_match'] is True for r in rs);low,high=wilson(correct,n)
        latency=[r['latency_s'] for r in rs if r['latency_s'] is not None]
        eligible=[r for r in rs if not r['reference_discrepancy']]
        result.append(dict(zip(keys,key),n=n,correct=correct,rate=correct/n,wilson_low=low,wilson_high=high,
            syntax_parse_fail=sum(r['parsed'] is False for r in rs),
            semantic_fail=sum(r['parsed'] is True and r['semantic_accepted'] is False for r in rs),
            interp_fail=sum(r['interpreted'] is False for r in rs),
            completed=sum(r['status']=='completed' for r in rs),
            pending=sum(r['status']=='pending_budget' for r in rs),
            provider_or_transport_fail=sum(r['status'] in ('provider_error','transport_error','interrupted_unknown_billing') for r in rs),
            cost_usd=sum(r['cost_usd'] for r in rs),
            mean_latency_s=statistics.mean(latency) if latency else None,
            n_without_discrepant_references=len(eligible),correct_without_discrepant_references=sum(r['ref_match'] is True for r in eligible)))
    return result


def export(run,references):
    m=load(run/'manifest.json');state=load(run/'state.json');refs={r['id']:r for r in load(references)}
    binary=REPO/'_build/default/evaluation/native/effects.exe';interpreter=REPO/'_build/default/bin/query_interp.exe';verifier=REPO/'_build/default/bin/verify.exe'
    modules=sorted(str(p) for p in (REPO/'modules').glob('*.type'))
    refprobes={key:probe(ref['formal_query'],binary) for key,ref in refs.items()}
    assert all(r['status']=='ok' for r in refprobes.values())
    grouped=defaultdict(list)
    for a in state['attempts']:grouped[a['cell_id']].append(a)
    cache={};verifycache={};rows=[];evidence={}
    for index,c in enumerate(m['cells']):
        ident=c['id'];model=m['config']['models'][c['model']];responsepath=run/'responses'/(ident+'.json')
        response=load(responsepath) if responsepath.exists() else {'status':'pending_budget','text':''}
        attempt_records=[]
        for a in grouped[ident]:
            p=run/'attempts'/(ident+f'--attempt{a["attempt"]}.json')
            if p.exists():attempt_records.append(load(p))
        text=response.get('text','');qh=digest(text.encode());ref=refs[c['task_id']]
        assert c['messages'][-1]['content']==ref['natural_language']
        parsed=semantic=interpreted=refmatch=None;nl='not_scored';err=[];vs=None
        if response['status'] in ('completed','incomplete') or text:
            if qh not in cache:
                try:generated=probe(text,binary)
                except Exception as e:generated={'status':'driver_error','error':type(e).__name__}
                with tempfile.TemporaryDirectory() as tmp:
                    q=Path(tmp)/'query.fql';q.write_text(text)
                    try:
                        p=subprocess.run([str(interpreter),str(q),'--',*modules],capture_output=True,text=True,timeout=30)
                        inter={'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
                    except subprocess.TimeoutExpired:inter={'returncode':None,'error':'TimeoutExpired'}
                cache[qh]={'probe':generated,'interpretation':inter}
            diag=cache[qh];g=diag['probe'];inter=diag['interpretation']
            parsed=g.get('parsed',g['status'] in ('ok','semantic_error','empty_query'))
            semantic=g['status']=='ok';interpreted=semantic and inter.get('returncode')==0
            refmatch=semantic and g.get('effects')==refprobes[c['task_id']]['effects']
            if semantic:nl=directory_obligations(ref['natural_language'],g['effects'])['status']
            else:nl='not_scored_invalid_query'
            if not semantic:err.append('native: '+g.get('error',g['status']))
            if not interpreted:err.append('interpretation: '+inter.get('error',str(inter.get('returncode'))))
            vk=(qh,c['task_id'])
            if vk not in verifycache:
                try:v=verify(text,ref['reference_solution'],verifier)
                except subprocess.TimeoutExpired:v={'status':'timeout','returncode':None}
                verifycache[vk]=v
            vs=verifycache[vk]['status']
            evidence[ident]={'query_sha256':qh,'probe_key':qh,'reference_program':verifycache[vk]}
        for a in attempt_records:
            if a.get('error'):err.append(f'attempt {a["attempt"]}: '+a['error'])
            elif a['status'] not in ('completed','incomplete'):err.append(f'attempt {a["attempt"]}: '+a['status'])
        if response['status']=='pending_budget':err.append('Budget/in-flight capacity prevented attempt; resumable')
        inp,out,reason=totals(attempt_records,model['provider'])
        # Reconcile historical cache-write detail without releasing any unknown-billing reserve.
        from matrix_run import usage_cost
        reconciled=0.0
        by_attempt={a['attempt']:a for a in attempt_records}
        for a in grouped[ident]:
            old=a.get('cost_usd',a['reserved_usd'])
            if a.get('cost_source')=='reported_tokens_at_frozen_rates' and a['attempt'] in by_attempt:
                old=usage_cost(by_attempt[a['attempt']],model,a['reserved_usd'])[0]
            reconciled+=old
        rows.append({'model':model['id'],'model_key':c['model'],'variant':c['variant'],'task_id':c['task_id'],'repeat':c['repeat'],
            'status':response['status'],'parsed':parsed,'semantic_accepted':semantic,'interpreted':interpreted,'ref_match':refmatch,'nl_obligation':nl,
            'input_tokens':inp,'output_tokens':out,'reasoning_tokens':reason,
            'cost_usd':reconciled,
            'latency_s':sum(a['seconds'] for a in grouped[ident]) if grouped[ident] and all('seconds' in a for a in grouped[ident]) else None,
            'attempts':len(grouped[ident]),
            'tokens_complete':len(attempt_records)==len(grouped[ident]) and bool(attempt_records) and all(isinstance(a.get('usage'),dict) for a in attempt_records) and all(a.get('cost_source')=='reported_tokens_at_frozen_rates' for a in grouped[ident]),
            'cost_sources':';'.join(sorted({a.get('cost_source','conservative_pending') for a in grouped[ident]})),
            'error':' | '.join(err),
            'reference_discrepancy':c['task_id'] in ('a03','a20'),
            'reference_program_status':vs,'output_sha256':qh if response['status'] in ('completed','incomplete') or text else None,
            'returned_model':response.get('returned_model'),
            'reasoning_effort':model.get('reasoning_effort'),'cost_is_estimate':True})
        if index%250==0:print(f'Scored {index}/{len(m["cells"])}',flush=True)
    rows.sort(key=lambda r:(r['model'],r['variant'],r['task_id'],r['repeat']))
    (run/'per-call.json').write_text(json.dumps(rows,indent=2)+'\n');write_csv(run/'per-call.csv',rows)
    summary=summarize(rows,['model','variant']);write_csv(run/'model-variant-summary.csv',summary)
    write_csv(run/'task-model-variant.csv',summarize(rows,['task_id','model','variant']))
    (run/'diagnostics-private.json').write_text(json.dumps({'reference_probes':refprobes,'query_diagnostics':cache,'cells':evidence},indent=2)+'\n')
    costs={'by_model':{model:sum(r['cost_usd'] for r in rows if r['model']==model) for model in sorted({r['model'] for r in rows})},
           'matrix_cost_usd':sum(r['cost_usd'] for r in rows),'prior_cost_reserve_usd':state['prior_cost_usd'],
           'budget_accounted_usd':state['prior_cost_usd']+sum(r['cost_usd'] for r in rows),
           'cache_detail_reconciliation_usd':sum(r['cost_usd'] for r in rows)-sum(a.get('cost_usd',a['reserved_usd']) for a in state['attempts']),
           'rates':m['config']['models'],'manifest_sha256':digest(m),
           'runner_sha256':digest((REPO/'evaluation/code/matrix_run.py').read_bytes()),
           'exporter_sha256':digest(Path(__file__).read_bytes()),
           'binary_sha256':{str(p.relative_to(REPO)):digest(p.read_bytes()) for p in [binary,interpreter,verifier]},
           'module_sha256':{str(Path(p).relative_to(REPO)):digest(Path(p).read_bytes()) for p in modules},
           'sources':m['sources'],'repetitions':m['repetitions'],
           'pricing_notes':'Token-based estimates at frozen rates, not invoices; missing usage charged full reservation. Router rates assume USD/MTok. Cost includes retries.',
           'correctness':'Primary correct = structural normalized reference-effect match, not program-execution correctness or general user-intent adequacy.',
           'reference_discrepancies':{'a03':'Supplied reference playbook fails native lowering (templated state string/file_state).','a20':'Supplied reference playbook rejects; eight-space sudoers separator vs tab diagnostic. Original references unchanged.'}}
    pending=[c for c in m['cells'] if c['model']=='opus' and not (run/'responses'/(c['id']+'.json')).exists()]
    left=sum(__import__('evaluate').reserve(c,m['config']) for c in pending)
    spent=state['prior_anthropic_cost_usd']+costs['by_model'].get(m['config']['models']['opus']['id'],0)
    costs['anthropic_remaining']={'cells':len(pending),'conservative_additional_cost_usd':left,
        'already_accounted_usd':spent,'guard_headroom_usd':max(0,22-spent),
        'topup_to_resume_with_2_usd_reserve_assuming_initial_24_usd':math.ceil(max(0,spent+left-22)*100)/100,
        'note':'Exact invoice/balance unknown. Top-up is conservative reservation arithmetic, including unknown-billing attempts.'}
    (run/'metadata.json').write_text(json.dumps(costs,indent=2)+'\n')
    print(json.dumps({'summary':summary,'costs':costs['by_model'],'remaining':costs['anthropic_remaining']},indent=2),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',type=Path,required=True);p.add_argument('--references',type=Path,required=True);a=p.parse_args();export(a.run,a.references)

if __name__=='__main__':main()
