#!/usr/bin/env python3
"""Private prior-work NL filtering -> sampled FQL generation -> native validity counts."""
import argparse
from collections import Counter,defaultdict
from concurrent.futures import ThreadPoolExecutor,as_completed
import copy
from datetime import datetime,timezone
import fcntl
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import time
import urllib.request
import evaluate as ev
from matrix_run import Matrix,retryable
from dataset_filter import candidate,normalize,support_hint
import dataset_transport as transport
from semantic_audit import probe
from export_matrix import totals,write_csv

ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent
REASONS={'concrete_self_contained','vague_object','missing_path','missing_source_or_destination','missing_value_or_content','missing_condition_or_context','ambiguous_action','other_missing_detail'}
SEED=20261112
SOURCE='/tmp/AnsibleDataset/withheld_ftdata-new.json'


def now():return datetime.now(timezone.utc).isoformat()


def save(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(obj,indent=2)+'\n')


def cost(state):return sum(a.get('cost_usd',a['reserved_usd']) for a in state['attempts'])


def credentials(path):
    values=ev.load(path)
    os.environ.update({k:v for k,v in values.items() if k in {'OPENAI_API_KEY','ANTHROPIC_API_KEY','AGENTFANCLUB_API_KEY','AGENTFANCLUB_BASE_URL'}})


def model_config(run):
    config=copy.deepcopy(ev.load(ROOT/'configs/models.json'));catalog_path=run/'private/router-catalog.json'
    if not catalog_path.exists():
        req=urllib.request.Request('https://api.router.agentfan.club/api/models',headers={'Authorization':'Bearer '+os.environ['AGENTFANCLUB_API_KEY'],'User-Agent':'Astrogator-Evaluation/1.0'})
        with urllib.request.urlopen(req,timeout=60) as response:save(catalog_path,json.load(response))
    catalog=ev.load(catalog_path)
    for key,m in config['models'].items():
        m['pricing_checked']='2026-11-12'
        if m['provider']=='agentfanclub':
            c=catalog[m['id']];assert c['limit']['output']>=32768
            for dest,source in [('input_per_million','input'),('output_per_million','output'),('cached_input_per_million','cache_read'),('cache_write_per_million','cache_write')]:m[dest]=c['cost'][source]
            m['catalog_limits']=c['limit']
    config['generation_model_workers']={'deepseek-v4.1-flash':32,'qwen3.8-flash':32,'deepseek-v4-flash':24,'glm-5.3':24,'sol':8,'opus':8}
    config.update(repetitions=1,max_output_tokens=32768,stream_deadline_s=3600,prior_cost_usd=0,prior_anthropic_cost_usd=0,total_budget_usd=20,provider_budgets_usd={'anthropic':8})
    return config


def prepare(run,source,prefix_batches=None):
    private=run/'private';target=private/'filter/manifest.json'
    if target.exists():return ev.load(target)
    rows=ev.load(source);assert isinstance(rows,list)
    rows=[{'input':row} if isinstance(row,str) else row for row in rows]
    origin=str(source.resolve())
    records=[];unique={}
    for index,row in enumerate(rows):
        keep,why,nl=candidate(row);original=row.get('input','')
        record={'task_id':f'd{index:05d}','source_path':origin,'repo_path':row.get('path',''),'row_index':index,
          'input_sha256':ev.digest(original.encode()) if isinstance(original,str) else ev.digest(original),
          'nl_sha256':ev.digest(nl.encode()),'heuristic_keep':keep,'heuristic_reason':why,'nl':nl,'fql_support_hint':support_hint(nl)}
        records.append(record)
        if keep:unique.setdefault(record['nl_sha256'],nl)
    labels={digest:{'id':f'n{i:05d}','nl':nl} for i,(digest,nl) in enumerate(sorted(unique.items()))}
    for r in records:
        if r['heuristic_keep']:r['classifier_id']=labels[r['nl_sha256']]['id']
    prompt=(ROOT/'prompts/detail-filter-v1.txt').read_text();config=model_config(run)
    config['models']={'deepseek-v4-flash':copy.deepcopy(config['models']['deepseek-v4-flash'])};config['models']['deepseek-v4-flash']['reasoning_effort']='low';config['max_output_tokens']=4096
    values=list(labels.values());cells=[]
    for n,start in enumerate(range(0,len(values),20)):
        batch=values[start:start+20];cells.append({'id':f'detail-b{n:05d}','model':'deepseek-v4-flash','variant':'detail-filter-v1',
            'task_id':f'b{n:05d}','repeat':0,'label_ids':[r['id'] for r in batch],
            'messages':[{'role':'system','content':prompt},{'role':'user','content':json.dumps(batch)}]})
    if prefix_batches is not None:cells=cells[:prefix_batches]
    manifest={'schema_version':1,'hash_prefix_batches':prefix_batches,'phase':'NL-only detail filter','created_at':now(),'config':config,'cells':cells,
       'source':{'source_path':origin,'file_sha256':ev.digest(source.read_bytes()),'total_rows':len(rows),'unique_survivor_nl':len(unique)},
       'sources':{'prompt_sha256':ev.digest(prompt.encode()),'rubric_sha256':ev.digest((ROOT/'docs/dataset-detail-rubric.md').read_bytes()),
          'heuristics_sha256':ev.digest((ROOT/'code/dataset_filter.py').read_bytes()),'driver_sha256':ev.digest(Path(__file__).read_bytes())}}
    save(private/'rows.json',records);save(private/'filter/manifest.json',manifest)
    print(json.dumps({'total':len(rows),'heuristic_reasons':dict(Counter(r['heuristic_reason'] for r in records)),
        'unique_survivor_nl':len(unique),'classifier_batches':len(cells),'classifier_reservation_envelope_usd':sum(ev.reserve(c,config) for c in cells)},indent=2),flush=True)
    return manifest


def classify_request(cell,config):
    result=transport.request(cell,config)
    if result['status']!='completed':
        # A classifier contract failure is retried, never treated as a negative detail label.
        result.update(status='transport_error');result.setdefault('error','classifier_output_incomplete');return result
    try:
        labels=json.loads(result['text']);assert isinstance(labels,list) and len(labels)==len(cell['label_ids'])
        assert [r['id'] for r in labels]==cell['label_ids']
        for r in labels:
            assert set(r)=={'id','keep','reason'} and type(r['keep']) is bool and r['reason'] in REASONS
            assert r['keep']==(r['reason']=='concrete_self_contained')
        result['labels']=labels
    except (ValueError,AssertionError,TypeError,KeyError):result.update(status='transport_error',error='classifier_format_error')
    return result


def matrix(manifest,out,total,anthropic,workers,request,worker_overrides=None):
    out.mkdir(parents=True,exist_ok=True)
    with (out/'.matrix.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        # Canonical exhausted transient receipts can resume up to eight attempts; immutable attempt history is retained.
        for terminal in (out/'responses').glob('*.json'):
            result=ev.load(terminal)
            if retryable(result) and result.get('attempt',8)<8:
                history=out/'terminal-history';history.mkdir(exist_ok=True)
                terminal.replace(history/(terminal.stem+f'--after{result["attempt"]}.json'))
        runner=Matrix(manifest,out,total,anthropic,8,request,transport.build)
        if manifest.get('phase')=='NL-to-FQL dataset validity':
            parallel_generate(runner,worker_overrides)
        else:runner.run(workers)


def parallel_generate(runner,overrides=None):
    """One durable ledger, model-local readmission after temporary reservations settle."""
    limits={**runner.manifest['config']['generation_model_workers'],**(overrides or {})}
    history=runner.out/'execution-settings.json';invocations=ev.load(history) if history.exists() else []
    invocations.append({'started_at':now(),'model_workers':limits,'scheduler':'independent per-model readmission','max_attempts':runner.max_attempts,'total_budget_usd':runner.total,'anthropic_budget_usd':runner.anthropic});save(history,invocations)
    def generate_model(model):
        cells=[c for c in runner.manifest['cells'] if c['model']==model];cell_ids={c['id'] for c in cells}
        provider=runner.manifest['config']['models'][model]['provider']
        while True:
            pending=[c for c in cells if not (runner.out/'responses'/(c['id']+'.json')).exists()]
            if not pending:return
            with runner.lock:before=sum(a['cell_id'] in cell_ids for a in runner.state['attempts'])
            with ThreadPoolExecutor(max_workers=limits[model]) as pool:
                for future in as_completed([pool.submit(runner.process,c) for c in pending]):future.result()
            with runner.lock:
                after=sum(a['cell_id'] in cell_ids for a in runner.state['attempts'])
                inflight=any(a['status']=='in_flight' for a in runner.state['attempts'])
                own_inflight=any(a['status']=='in_flight' and a['provider']==provider for a in runner.state['attempts'])
                own_guard=provider=='anthropic' and all(runner.spend(provider)+ev.reserve(c,runner.manifest['config'])>runner.anthropic+1e-9 for c in pending)
            if after==before:
                if (own_guard and not own_inflight) or not inflight:return
                time.sleep(1)
    with ThreadPoolExecutor(max_workers=len(limits)) as controller:
        futures=[controller.submit(generate_model,model) for model in limits]
        for future in as_completed(futures):future.result()
    terminal=sum((runner.out/'responses'/(c['id']+'.json')).exists() for c in runner.manifest['cells'])
    status={'planned':len(runner.cells),'terminal':terminal,'pending':len(runner.cells)-terminal,
       'attempts':len(runner.state['attempts']),'accounted_usd':runner.spend(),
       'anthropic_accounted_usd':runner.spend('anthropic'),'total_limit_usd':runner.total,
       'anthropic_limit_usd':runner.anthropic,'model_workers':limits}
    save(runner.out/'run-status.json',status);print(json.dumps(status),flush=True)


def select(run,prefix_batches=None):
    private=run/'private'
    if (private/'generation/manifest.json').exists():
        print('Sample already frozen for generation; preserving row selection',flush=True)
        return ev.load(private/'sample.json')
    rows=ev.load(private/'rows.json');m=ev.load(private/'filter/manifest.json');labels={}
    for c in m['cells']:
        p=private/'filter/responses'/(c['id']+'.json')
        result=ev.load(p) if p.exists() else {}
        if result.get('status')=='completed':
            for label in result['labels']:labels[label['id']]={**label,'classifier_cell_id':c['id']}
    for r in rows:
        label=labels.get(r.get('classifier_id'))
        r.update(detail_status='not_checked_heuristic_drop' if not r['heuristic_keep'] else ('resolved' if label else 'unresolved'),
          detail_keep=label['keep'] if label else False,detail_reason=label['reason'] if label else r['heuristic_reason'] if not r['heuristic_keep'] else 'classifier_unresolved',
          classifier_cell_id=label.get('classifier_cell_id') if label else None)
    for r in rows:r['in_filter_subset']=r['heuristic_keep'] and (prefix_batches is None or int(r['classifier_id'][1:])<prefix_batches*20)
    population=[r for r in rows if r['in_filter_subset']]
    if prefix_batches is not None:assert all(r['detail_status']=='resolved' for r in population),'The fixed filter subset must have every label before sampling'
    kept=[r for r in population if r['detail_keep']];sample=random.Random(SEED).sample(kept,min(300,len(kept)))
    sampled={r['task_id'] for r in sample}
    for r in rows:r['sampled']=r['task_id'] in sampled
    save(private/'filtered-rows.json',rows);save(private/'sample.json',sample)
    funnel={'total':len(rows),'after_heuristics':sum(r['heuristic_keep'] for r in rows),'after_detail_check':len(kept),'sampled':len(sample),
       'unique_heuristic_survivor_nl':m['source']['unique_survivor_nl'],'classifier_batches':len(m['cells']),
       'filter_subset_rows':len(population),'filter_subset_unique_nl':len({r['nl_sha256'] for r in population}),
       'rows_classified_in_subset':sum(r['detail_status']=='resolved' for r in population),
       'rows_classified_total':sum(r['detail_status']=='resolved' for r in rows),
       'kept_total_collected':sum(r['detail_keep'] for r in rows),
       'classified_outside_subset':sum(r['detail_status']=='resolved' and not r['in_filter_subset'] for r in rows),
       'filter_subset_rule':'All rows whose surviving normalized-NL SHA256 is in the first '+str(prefix_batches*20)+' sorted distinct digests' if prefix_batches is not None else 'All heuristic survivors',
       'hash_prefix_batches':prefix_batches,
       'detail_unresolved_rows':sum(r['detail_status']=='unresolved' for r in population),'heuristic_reasons':dict(Counter(r['heuristic_reason'] for r in rows)),
       'detail_reasons':dict(Counter(r['detail_reason'] for r in population)),'sample_seed':SEED}
    save(private/'funnel.json',funnel);print(json.dumps(funnel,indent=2),flush=True)
    return sample


def freeze_generation(run):
    private=run/'private';path=private/'generation/manifest.json'
    if path.exists():return ev.load(path)
    sample=ev.load(private/'sample.json');assert sample,'No kept rows to generate'
    demos=ev.load(ROOT/'prompts/fixed-fql-demos-v1.json');system=(ROOT/'prompts/handbook-v3.txt').read_text()
    config=model_config(run);filter_cost=cost(ev.load(private/'filter/state.json'));config['prior_cost_usd']=filter_cost
    cells=[]
    for row in sample:
        assert row['nl'] not in {d['nl'] for d in demos['demonstrations']},'Exact demonstration collision requires explicit exclusion'
        messages=[{'role':'system','content':system}]
        for d in demos['demonstrations']:messages.extend([{'role':'user','content':d['nl']},{'role':'assistant','content':d['fql']}])
        messages.append({'role':'user','content':row['nl']})
        for model in config['models']:
            cells.append({'id':f'{model}--handbook-v3--{row["task_id"]}--r0','model':model,'variant':'handbook-v3','task_id':row['task_id'],
                'repeat':0,'demonstration_ids':[d['id'] for d in demos['demonstrations']],'messages':messages})
    priority={'deepseek-v4.1-flash':0,'qwen3.8-flash':1,'deepseek-v4-flash':2,'glm-5.3':3,'sol':4,'opus':5}
    cells.sort(key=lambda c:(priority[c['model']],ev.digest(c['id'])))
    m={'schema_version':1,'phase':'NL-to-FQL dataset validity','created_at':now(),'config':config,'cells':cells,'repetitions':1,
       'scope':'Counts of nonempty grammar parsing, semantic acceptance and native symbolic interpretation only; no reference or execution comparison',
       'sources':{'handbook_sha256':ev.digest(system.encode()),'demos_sha256':ev.digest((ROOT/'prompts/fixed-fql-demos-v1.json').read_bytes()),
          'source_file_sha256':ev.load(private/'filter/manifest.json')['source']['file_sha256'],'sample_sha256':ev.digest([{k:v for k,v in r.items() if k!='nl'} for r in sample]),
          'transport_sha256':ev.digest((ROOT/'code/dataset_transport.py').read_bytes()),'driver_sha256':ev.digest(Path(__file__).read_bytes())}}
    for source in [Path(__file__),ROOT/'code/dataset_transport.py',ROOT/'prompts/handbook-v3.txt',ROOT/'prompts/fixed-fql-demos-v1.json']:
        snapshot=private/'generation/source'/source.name;snapshot.parent.mkdir(parents=True,exist_ok=True);snapshot.write_bytes(source.read_bytes())
    save(path,m);print(json.dumps({'sampled':len(sample),'planned_generation_calls':len(cells),'prior_classifier_cost_usd':filter_cost,
        'max_token_envelope_not_expected_cost':ev.estimate(m)},indent=2),flush=True)
    return m


def stop_reason(response):
    raw=response.get('response',{});return raw.get('stop_reason') or raw.get('status') or (raw.get('choices') or [{}])[0].get('finish_reason')


def score(run,workers):
    private=run/'private';m=ev.load(private/'generation/manifest.json');binary=REPO/'_build/default/evaluation/native/effects.exe';interp=REPO/'_build/default/bin/query_interp.exe';assert binary.exists() and interp.exists(),'Build the native diagnostics first'
    modules=sorted(str(p) for p in (REPO/'modules').glob('*.type'));texts={}
    for c in m['cells']:
        p=private/'generation/responses'/(c['id']+'.json')
        if p.exists():
            r=ev.load(p)
            if r['status'] in ('completed','incomplete'):texts[ev.digest(r['text'].encode())]=r['text']
    cache_dir=private/'diagnostics';cache_dir.mkdir(exist_ok=True)
    def check(item):
        digest,text=item;path=cache_dir/(digest+'.json')
        if path.exists():return
        try:g=probe(text,binary)
        except (subprocess.TimeoutExpired,OSError) as error:g={'status':'driver_error','error':type(error).__name__,'parsed':False}
        parsed=bool(g.get('parsed')) and g['status']!='empty_query';semantic=bool(g.get('semantic_accepted',g['status']=='ok'));native=None
        if semantic:
            with tempfile.TemporaryDirectory(prefix='dataset-fql-') as tmp:
                q=Path(tmp)/'query.fql';q.write_text(text)
                try:
                    p=subprocess.run([str(interp),str(q),'--',*modules],capture_output=True,text=True,timeout=30);native={'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
                except subprocess.TimeoutExpired:native={'returncode':None,'error':'native_interpretation_timeout'}
        save(path,{'probe':g,'parsed':parsed,'semantic_accepted':semantic,'interpreter_attempted':semantic,'interpreted':semantic and native.get('returncode')==0,'native':native})
    with ThreadPoolExecutor(max_workers=workers) as pool:list(pool.map(check,texts.items()))
    print(json.dumps({'unique_outputs_scored':len(texts),'reference_comparison':False,'output_judge':False}),flush=True)


def public_attempts(run,phase,manifest):
    private=run/'private'/phase;state=ev.load(private/'state.json');cells={c['id']:c for c in manifest['cells']};rows=[]
    for a in state['attempts']:
        c=cells[a['cell_id']];p=private/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json');r=ev.load(p) if p.exists() else {}
        inp,out,reasoning=totals([r],a['provider']);model=manifest['config']['models'][c['model']]
        rows.append({'phase':phase,'cell_id':a['cell_id'],'model':model['id'],'attempt':a['attempt'],'status':a['status'],
          'http_status':r.get('http_status'),'input_tokens':inp,'output_tokens':out,'reasoning_tokens':reasoning,
          'cost_usd':a.get('cost_usd',a['reserved_usd']),'cost_source':a.get('cost_source'),'latency_s':a.get('seconds'),
          'started_at':a['started_at'],'request_sha256':ev.digest(a['request_body']),'stop_reason':stop_reason(r),'error':r.get('error','')})
    return rows


def export(run):
    private=run/'private';fm=ev.load(private/'filter/manifest.json');m=ev.load(private/'generation/manifest.json');allrows=ev.load(private/'filtered-rows.json');sample={r['task_id']:r for r in ev.load(private/'sample.json')};state=ev.load(private/'generation/state.json');attempts=defaultdict(list)
    for a in state['attempts']:attempts[a['cell_id']].append(a)
    cases=[]
    for r in allrows:cases.append({k:v for k,v in r.items() if k!='nl'})
    write_csv(run/'filter-decisions.csv',cases)
    write_csv(run/'sample-ids.csv',[{k:v for k,v in r.items() if k!='nl'} for r in sample.values()])
    rows=[];diagpublic=[];outputs=[]
    for c in m['cells']:
        ident=c['id'];rpath=private/'generation/responses'/(ident+'.json');response=ev.load(rpath) if rpath.exists() else {'status':'pending_budget','text':''};text=response.get('text','');digest=ev.digest(text.encode());src=sample[c['task_id']];model=m['config']['models'][c['model']]
        gpath=private/'diagnostics'/(digest+'.json');g=ev.load(gpath) if response['status'] in ('completed','incomplete') and gpath.exists() else {}
        receipts=[ev.load(private/'generation/attempts'/(ident+f'--attempt{a["attempt"]}.json')) for a in attempts[ident]]
        inp,out,reason=totals(receipts,model['provider']);path=None
        if response['status'] in ('completed','incomplete'):
            dest=run/'outputs'/model['id']/(c['task_id']+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(text);path=str(dest.relative_to(run))
        row={**{k:src[k] for k in ['task_id','source_path','repo_path','row_index','input_sha256','nl_sha256','fql_support_hint']},
          'cell_id':ident,'model':model['id'],'variant':'handbook-v3','repeat':0,'status':response['status'],'stop_reason':stop_reason(response),
          'parsed':g.get('parsed'),'semantic_accepted':g.get('semantic_accepted'),'interpreted':g.get('interpreted'),'interpreter_attempted':g.get('interpreter_attempted',False),
          'api_failure':response['status'] in ('provider_error','transport_error','interrupted_unknown_billing'),
          'output_nonempty':bool(text.strip()),'output_path':path,'output_sha256':digest if path else None,
          'input_tokens':inp,'output_tokens':out,'reasoning_tokens':reason,'cost_usd':sum(a.get('cost_usd',a['reserved_usd']) for a in attempts[ident]),
          'latency_s':sum(a.get('seconds',0) for a in attempts[ident]),'attempts':len(attempts[ident]),'max_output_tokens':32768,
          'reasoning_effort':model['reasoning_effort'],'returned_model':response.get('returned_model'),
          'messages_sha256':ev.digest(c['messages']),'error':response.get('error','') or g.get('probe',{}).get('error','') or ((g.get('native') or {}).get('error',''))}
        rows.append(row);outputs.append({'cell_id':ident,'output':text if path else None,'status':response['status'],'output_sha256':row['output_sha256']})
        if g:diagpublic.append({'cell_id':ident,'output_sha256':digest,'parse_semantic_status':g['probe']['status'],'parse_semantic_error':g['probe'].get('error'),
            'native_returncode':(g.get('native') or {}).get('returncode'),'native_stdout':(g.get('native') or {}).get('stdout'),'native_stderr':(g.get('native') or {}).get('stderr')})
    rows.sort(key=lambda r:(r['model'],r['row_index']));write_csv(run/'per-cell.csv',rows);save(run/'per-cell.json',rows)
    summary=[]
    for model in sorted({r['model'] for r in rows}):
        rs=[r for r in rows if r['model']==model];summary.append({'model':model,'n':len(rs),'completed':sum(r['status']=='completed' for r in rs),
          'incomplete':sum(r['status']=='incomplete' for r in rs),'parsed':sum(r['parsed'] is True for r in rs),
          'semantic_accepted':sum(r['semantic_accepted'] is True for r in rs),'interpreted':sum(r['interpreted'] is True for r in rs),
          'api_failures':sum(r['api_failure'] for r in rs),'pending_budget':sum(r['status']=='pending_budget' for r in rs),
          'cost_usd':sum(r['cost_usd'] for r in rs),'mean_latency_s':sum(r['latency_s'] for r in rs if r['attempts'])/max(1,sum(bool(r['attempts']) for r in rs))})
    write_csv(run/'model-summary.csv',summary)
    filter_attempts=public_attempts(run,'filter',fm);generation_attempts=public_attempts(run,'generation',m)
    write_csv(run/'per-attempt.csv',filter_attempts+generation_attempts)
    classifier_outputs=[]
    for c in fm['cells']:
        path=private/'filter/responses'/(c['id']+'.json')
        if path.exists():
            result=ev.load(path);classifier_outputs.append({'cell_id':c['id'],'label_ids':c['label_ids'],'status':result['status'],'output':result.get('text','')})
    save(run/'classifier-outputs.json',classifier_outputs);save(run/'native-diagnostics.json',diagpublic)
    fcost=cost(ev.load(private/'filter/state.json'));gcost=cost(state);total=fcost+gcost;anthropic=sum(a.get('cost_usd',a['reserved_usd']) for a in state['attempts'] if a['provider']=='anthropic')
    assert total<=20+1e-8 and anthropic<=8+1e-8
    unknown=sum(a['cost_usd'] for a in filter_attempts+generation_attempts if a['cost_source']!='reported_tokens_at_frozen_rates')
    manifest={'experiment':'Prior-work NL-to-FQL dataset validity only','created_at':m['created_at'],'exported_at':now(),'source':fm['source'],
      'funnel':ev.load(private/'funnel.json'),'models':m['config']['models'],'settings':{'variant':'handbook-v3','sample_seed':SEED,'samples_per_model_task':1,
        'max_output_tokens':32768,'reasoning_effort':'HIGH; Qwen XHIGH','temperature':None,'top_p':None,'seed':None,
        'demonstration_policy':'Fixed first recovered target set a13,a02,a03,a19; old 21-task matrix used target-specific sets',
        'initial_generation_model_workers':m['config']['generation_model_workers'],
        'generation_invocations':ev.load(private/'generation/execution-settings.json') if (private/'generation/execution-settings.json').exists() else [],
        'demonstration_ids':['a13','a02','a03','a19'],'filter_model':'deepseek-v4-flash','filter_effort':'low','filter_max_output_tokens':4096,'filter_batch_size':20,'max_attempts':8},
      'sources':{**m['sources'],**{'filter_'+k:v for k,v in fm['sources'].items()}},'budget_guards':{'total_usd':20,'anthropic_usd':8},
      'costs':{'classifier_usd':fcost,'generation_usd':gcost,'total_accounted_usd':total,'anthropic_usd':anthropic,'unknown_billing_reserve_usd':unknown,
        'notes':'Token-based local accounting at frozen rates, not invoices; router catalog units assumed USD/MTok. Includes transient retries; no prior experiments charged to this run.'},
      'native':{'parse_definition':'Nonempty grammar parse; semantic-error queries can parse. Empty query counts false.',
        'semantic_definition':'Existing analyze_top returns Ok; stage flag retained independently of effect serialization errors.',
        'interpretation_definition':'Semantic accepted and native query_interp exits zero; symbolic interpretation, no managed-host execution.',
        'effects_binary_sha256':ev.digest((REPO/'_build/default/evaluation/native/effects.exe').read_bytes()),'query_interp_binary_sha256':ev.digest((REPO/'_build/default/bin/query_interp.exe').read_bytes()),
        'module_sha256':{str(p.relative_to(REPO)):ev.digest(p.read_bytes()) for p in sorted((REPO/'modules').glob('*.type'))}},
      'summary':summary,'privacy':'Source dataset, original NL/YAML, complete message manifests and raw provider reasoning remain private; only IDs/hashes, model outputs and counts exported.',
      'operator_events':ev.load(private/'operator-events.json') if (private/'operator-events.json').exists() else [],
      'correctness_claim':False,'reference_comparison':False,'output_judge':False,'runtime_execution':False}
    for source in (private/'generation/source').glob('*'):
        target=run/'sources'/source.name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source.read_bytes())
    for source in [ROOT/'prompts/detail-filter-v1.txt',ROOT/'docs/dataset-detail-rubric.md']:
        target=run/'sources'/source.name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source.read_bytes())
    save(run/'manifest.json',manifest)
    print(json.dumps({'funnel':manifest['funnel'],'costs':manifest['costs'],'summary':summary},indent=2),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('command',choices=['prepare','filter','sample','generate','score','export','all']);p.add_argument('--run',type=Path,required=True)
    p.add_argument('--deepseek-v4-workers',type=int);p.add_argument('--hash-prefix-batches',type=int);p.add_argument('--source',type=Path);p.add_argument('--credentials-file',type=Path);p.add_argument('--workers',type=int,default=24);a=p.parse_args();private=a.run/'private'
    if a.credentials_file:credentials(a.credentials_file)
    if a.command=='all':
        assert all((REPO/p).exists() for p in ['_build/default/evaluation/native/effects.exe','_build/default/bin/query_interp.exe']),'Build native diagnostics before starting a funded run'
    if a.command in ('prepare','all'):prepare(a.run,a.source or private/'source/withheld_ftdata-new.json',a.hash_prefix_batches)
    if a.command in ('filter','all') and not (private/'generation/manifest.json').exists():
        m=ev.load(private/'filter/manifest.json');matrix(m,private/'filter',20,0,a.workers,classify_request)
    if a.command in ('sample','all'):select(a.run,a.hash_prefix_batches)
    if a.command in ('generate','all'):
        m=freeze_generation(a.run);overrides={'deepseek-v4-flash':a.deepseek_v4_workers} if a.deepseek_v4_workers else None
        matrix(m,private/'generation',20,8,a.workers,transport.request,overrides)
    if a.command in ('score','all'):score(a.run,min(8,a.workers))
    if a.command in ('export','all'):export(a.run)

if __name__=='__main__':main()
