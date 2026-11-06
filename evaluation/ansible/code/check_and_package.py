#!/usr/bin/env python3
"""Free extraction/YAML/syntax checks only. Never execute a generated playbook."""
import argparse
from collections import Counter,defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timedelta,timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import yaml
from generate import REPO,PROBLEMS
import evaluate as ev
from export_matrix import totals,write_csv

FORBIDDEN={'shell','command','raw','script'}
FENCES=re.compile('^```(yaml)?$',flags=re.MULTILINE)
VENV=Path(sys.prefix) if sys.prefix!=sys.base_prefix else Path('/tmp/astrogator-ansible-venv')


def extract(text):return re.sub(FENCES,'',text)


def parse_yaml(text):
    try:return True,yaml.load(text,Loader=yaml.BaseLoader),''
    except yaml.YAMLError as e:return False,None,str(e)


def forbidden(doc):
    found=set()
    def module(name):
        if isinstance(name,str):
            short=name.strip().split()[0].split('.')[-1] if name.strip() else ''
            if short in FORBIDDEN:found.add(short)
    def task(obj):
        if not isinstance(obj,dict):return
        for key in obj:module(key)
        for key in ('action','local_action'):
            action=obj.get(key)
            if isinstance(action,str):module(action)
            elif isinstance(action,dict):module(action.get('module',''))
        for key in ('block','rescue','always'):
            for child in obj.get(key,[]) if isinstance(obj.get(key),list) else []:task(child)
    def play(obj):
        if not isinstance(obj,dict):return
        recognized=False
        for key in ('tasks','pre_tasks','post_tasks','handlers'):
            if isinstance(obj.get(key),list):
                recognized=True
                for t in obj[key]:task(t)
        if not recognized:task(obj)
    for obj in doc if isinstance(doc,list) else [doc]:play(obj)
    return sorted(found)


def syntax_check(playbook):
    with tempfile.TemporaryDirectory(prefix='astrogator-syntax-') as tmp:
        work=Path(tmp);(work/'playbook.yml').write_bytes(Path(playbook).read_bytes())
        (work/'inventory').write_text('[debian]\nlocalhost\n[redhat]\nlocalhost\n[ubuntu]\nlocalhost\n')
        (work/'ansible.cfg').write_text('[defaults]\nlocal_tmp=/tmp/ansible-local\nhost_key_checking=False\n')
        command=['bwrap','--unshare-all','--die-with-parent','--clearenv',
          '--ro-bind','/usr','/usr','--ro-bind','/lib','/lib','--ro-bind','/lib64','/lib64',
          '--symlink','usr/bin','/bin','--proc','/proc','--dev','/dev','--tmpfs','/tmp',
          '--dir','/tmp/home','--dir','/etc','--ro-bind','/etc/passwd','/etc/passwd','--ro-bind','/etc/group','/etc/group',
          '--ro-bind',str(VENV),str(VENV),'--ro-bind',str(work),'/work','--chdir','/work',
          '--setenv','HOME','/tmp/home','--setenv','PATH',str(VENV/'bin')+':/usr/bin:/bin',
          '--setenv','ANSIBLE_CONFIG','/work/ansible.cfg','--setenv','ANSIBLE_NOCOLOR','1',
          '--setenv','ANSIBLE_LOCAL_TEMP','/tmp/ansible-local',
          str(VENV/'bin/ansible-playbook'),'--syntax-check','-i','/work/inventory','/work/playbook.yml']
        try:
            p=subprocess.run(command,capture_output=True,text=True,timeout=30)
            return {'syntax_check_pass':p.returncode==0,'syntax_check_status':'pass' if p.returncode==0 else 'fail',
                    'syntax_returncode':p.returncode,'syntax_stdout':p.stdout,'syntax_stderr':p.stderr}
        except subprocess.TimeoutExpired:return {'syntax_check_pass':False,'syntax_check_status':'timeout','syntax_returncode':None,'syntax_stdout':'','syntax_stderr':'Syntax check exceeded 30 seconds'}


def store(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():assert path.read_bytes()==data,'Existing sample differs: '+str(path)
    else:path.write_bytes(data)


def package(run,workers):
    private=run/'private';m=ev.load(private/'manifest.json');state=ev.load(private/'state.json')
    assert (private/'run-status.json').exists(),'Generation must finish or reach a guard first'
    attempts=defaultdict(list)
    for a in state['attempts']:attempts[a['cell_id']].append(a)
    models=m['config']['models'];data=[];completions=[]
    with tempfile.TemporaryDirectory(prefix='astrogator-paper-process-') as tmp:
        stage=Path(tmp)
        for c in m['cells']:
            key=c['model'];model=models[key]['id'];n=c['repeat'];p=private/'responses'/(c['id']+'.json')
            result=ev.load(p) if p.exists() else {'status':'budget_pending','text':''}
            actual=result.get('text','') if result['status'] in ('completed','incomplete') else ''
            stripped=extract(actual);raw_ok,doc,raw_error=parse_yaml(stripped) if stripped.strip() else (False,None,'No model YAML content')
            scan=forbidden(doc) if raw_ok else sorted(set(re.findall(r'^\s*(?:-\s*)?(?:ansible\.(?:builtin|legacy)\.)?(shell|command|raw|script)\s*:',stripped,re.M)))
            if actual.strip():
                dst=stage/model/c['problem']/f'raw{n}.yml';dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(stripped)
            records=[]
            for a in attempts[c['id']]:
                f=private/'attempts'/(c['id']+f'--attempt{a["attempt"]}.json')
                if f.exists():records.append(ev.load(f))
            inp,out,reason=totals(records,models[key]['provider'])
            cost=sum(a.get('cost_usd',a['reserved_usd']) for a in attempts[c['id']])
            start=attempts[c['id']][0]['started_at'] if attempts[c['id']] else None
            last=attempts[c['id']][-1] if attempts[c['id']] else None
            end=(datetime.fromisoformat(last['started_at'])+timedelta(seconds=last['seconds'])).isoformat() if last and 'seconds' in last else None
            row={'cell_id':c['id'],'model':model,'model_key':key,'task_id':c['task_id'],'problem':c['problem'],'sample':n,
                 'status':result['status'],'returned_model':result.get('returned_model'),
                 'prompt_sha256':ev.digest(c['messages'][0]['content'].encode()),'raw_text_sha256':ev.digest(actual.encode()),
                 'stop_reason':(result.get('response',{}).get('stop_reason') or result.get('response',{}).get('status') or (result.get('response',{}).get('choices') or [{}])[0].get('finish_reason')),
                 'raw_nonempty':bool(actual.strip()),'yaml_parses':raw_ok,'yaml_error':raw_error,
                 'extracted_nonempty':False,'processed_yaml_parses':None,'has_tasks':False,
                 'syntax_check_pass':None,'syntax_check_status':'not_extracted','syntax_returncode':None,
                 'forbidden_module_flag':bool(scan),'forbidden_modules':','.join(scan),
                 'module_scan':'structured raw YAML' if raw_ok else 'heuristic lines in invalid YAML',
                 'sample_path':None,'sha256':None,'input_tokens':inp,'output_tokens':out,'reasoning_tokens':reason,
                 'cost_usd':cost,'attempts':len(attempts[c['id']]),'started_at':start,'finished_at':end,
                 'latency_s':sum(a['seconds'] for a in attempts[c['id']]) if attempts[c['id']] and all('seconds' in a for a in attempts[c['id']]) else None,
                 'error':' | '.join(r.get('error',r['status']) for r in records if r['status'] not in ('completed','incomplete'))}
            data.append(row);completions.append({'cell_id':c['id'],'model':model,'problem':c['problem'],'sample':n,'status':result['status'],'text':actual})
        processor=REPO/'_build/default/evaluation/ansible/native/paper_process.exe'
        p=subprocess.run([str(processor),*[x['id'] for x in models.values()]],cwd=stage,capture_output=True,text=True,check=True)
        (private/'paper-processing.log').write_text(p.stdout+p.stderr)
        jobs=[]
        for row in data:
            relative=Path(row['model'])/row['problem']/f'response{row["sample"]}.yml';source=stage/relative
            if source.exists():
                dest=run/relative;store(dest,source.read_bytes());ok,obj,error=parse_yaml(dest.read_text())
                row.update(extracted_nonempty=bool(dest.read_text().strip()),processed_yaml_parses=ok,
                    has_tasks=isinstance(obj,list) and any(isinstance(play,dict) and isinstance(play.get('tasks'),list) and bool(play['tasks']) for play in obj),
                    sample_path=str(relative),sha256=ev.digest(dest.read_bytes()))
                scan=sorted(set(row['forbidden_modules'].split(','))- {''} | set(forbidden(obj)))
                row.update(forbidden_module_flag=bool(scan),forbidden_modules=','.join(scan));jobs.append((row,dest))
        def check(job):
            row,path=job;diag=syntax_check(path);row.update({k:v for k,v in diag.items() if k not in ('syntax_stdout','syntax_stderr')})
            dst=private/'syntax-diagnostics'/(row['cell_id']+'.json');dst.parent.mkdir(exist_ok=True);dst.write_text(json.dumps(diag,indent=2)+'\n')
            if diag['syntax_check_status']!='pass':row['error']=(row['error']+' | '+diag['syntax_stderr']).strip(' |')
        with ThreadPoolExecutor(max_workers=workers) as pool:list(pool.map(check,jobs))
    data.sort(key=lambda r:(r['model'],r['problem'],r['sample']));write_csv(run/'offline-checks.csv',[{**r,'error':r['error'].replace('\r','\\r').replace('\n','\\n'),'yaml_error':r['yaml_error'].replace('\r','\\r').replace('\n','\\n')} for r in data])
    (run/'raw-completions.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in completions))
    summary=[]
    for model in sorted({r['model'] for r in data}):
        rs=[r for r in data if r['model']==model]
        summary.append({'model':model,'planned':len(rs),'completed':sum(r['status']=='completed' for r in rs),
          'incomplete':sum(r['status']=='incomplete' for r in rs),'provider_or_transport_failures':sum(r['status'] in ('provider_error','transport_error','interrupted_unknown_billing') for r in rs),
          'budget_pending':sum(r['status']=='budget_pending' for r in rs),'raw_nonempty':sum(r['raw_nonempty'] for r in rs),
          'yaml_parses':sum(r['yaml_parses'] for r in rs),'extracted_nonempty':sum(r['extracted_nonempty'] for r in rs),
          'processed_yaml_parses':sum(r['processed_yaml_parses'] is True for r in rs),'has_tasks':sum(r['has_tasks'] for r in rs),
          'syntax_check_pass':sum(r['syntax_check_pass'] is True for r in rs),'syntax_check_fail':sum(r['syntax_check_pass'] is False for r in rs),
          'syntax_check_not_run':sum(r['syntax_check_pass'] is None for r in rs),'forbidden_module_flags':sum(r['forbidden_module_flag'] for r in rs),
          'cost_usd':sum(r['cost_usd'] for r in rs)})
    write_csv(run/'model-summary.csv',summary)
    byprovider=defaultdict(float);known=unknown=0
    for a in state['attempts']:
        charge=a.get('cost_usd',a['reserved_usd']);byprovider[a['provider']]+=charge
        if a.get('cost_source')=='reported_tokens_at_frozen_rates':known+=charge
        else:unknown+=charge
    assert sum(byprovider.values())<=25+1e-6 and byprovider.get('anthropic',0)<=15+1e-6
    public_attempts=[]
    for a in state['attempts']:
        path=private/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json')
        raw=ev.load(path) if path.exists() else {}
        public_attempts.append({**{k:v for k,v in a.items() if k!='request_body'},
            'token_usage':raw.get('usage'),'request_sha256':ev.digest(a['request_body']),
            'returned_model':raw.get('returned_model'),'error':raw.get('error')})
    public={'experiment':'Appendix B NL-to-Ansible generation only; no runtime evaluation or judge',
       'created_at':m['created_at'],'packaged_at':datetime.now(timezone.utc).isoformat(),'planned_cells':1260,
       'models':models,'settings':{'repeats':10,'max_output_tokens':4096,'temperature':None,'top_p':None,'seed':None,
          'prompt_role':'single user; no added system message','router_transport':'stream=true; include_usage=true; reasoning/content accumulated with final usage'},
       'prompt_template':m['prompt_template'],'prompt_sha256':m['sources']['prompt_sha256'],'tasks':m['tasks'],
       'sources':{**m['sources'],'paper_processor_original_sha256':ev.digest((REPO/'astrogator-eval/processing.ml').read_bytes()),
          'paper_processor_adapter_sha256':ev.digest((REPO/'evaluation/ansible/native/paper_process.ml').read_bytes()),
          'checker_sha256':ev.digest(Path(__file__).read_bytes())},
       'budget_guards':{'total_usd':25,'anthropic_usd':15},'cost_accounted_usd':sum(byprovider.values()),
       'reported_token_cost_usd':known,'unknown_billing_reserve_usd':unknown,'cost_by_provider':dict(byprovider),
       'cost_notes':'Exact local accounting at frozen model rates, not provider invoices; unknown billing remains conservatively reserved. Router catalog rates assume USD/MTok.',
       'offline_environment':{'ansible_core':'2.19.11','pyyaml':yaml.__version__,'syntax_check':'ansible-playbook --syntax-check; bwrap unshared process, no network/credentials/host home; builtin collections only','runtime_execution':False,'judge':False},
       'extraction':'Original new_extract.py fence regex then processing.ml task/handler/vars wrapper; adapter changes only model argv and missing raw-file guard; original input/output retained',
       'calls':data,'attempts':public_attempts,
       'summary':summary,'scope':'All checks are format/tool-acceptance checks, not correctness or VM test results'}
    (run/'manifest.json').write_text(json.dumps(public,indent=2)+'\n')
    print(json.dumps({'cost_accounted_usd':public['cost_accounted_usd'],'reported_token_cost_usd':known,'unknown_billing_reserve_usd':unknown,'summary':summary},indent=2),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',type=Path,required=True);p.add_argument('--workers',type=int,default=6);p.add_argument('--wait',action='store_true');a=p.parse_args()
    if a.wait:
        while not (a.run/'private/run-status.json').exists():time.sleep(10)
    package(a.run,a.workers)

if __name__=='__main__':main()
