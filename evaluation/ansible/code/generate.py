#!/usr/bin/env python3
"""Appendix B generation only: no tools, judge, verifier or playbook execution."""
import argparse
import copy
from datetime import datetime,timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import sys
import time
import urllib.error
import urllib.request

REPO=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(REPO/'evaluation/code'))
import evaluate as ev
from matrix_run import Matrix

PROBLEMS=[f'p{i:02}' for i in range(1,11)]+['p11a','p11b']+[f'p{i:02}' for i in range(12,21)]


def freeze(refs):
    prompt_path=REPO/'evaluation/ansible/prompts/appendix-b-v1.txt'
    template=prompt_path.read_text();source=ev.load(refs)
    assert {r['legacy_id'] for r in source}==set(PROBLEMS) and len(source)==21
    config=copy.deepcopy(ev.load(REPO/'evaluation/configs/models.json'))
    config.update(repetitions=10,max_output_tokens=4096,prior_cost_usd=0,prior_anthropic_cost_usd=0,
                  provider_budgets_usd={'anthropic':15},total_budget_usd=25)
    config['matrix_status']='Darsh approved generation only 2026-11-05; $25 total, $15 Anthropic; no runtime or judge'
    assert len(config['models'])==6
    tasks=[{'task_id':r['id'],'problem':r['legacy_id'],'description':r['natural_language']} for r in source]
    cells=[]
    for t in tasks:
        message=template.replace('{ task }',t['description'])
        for model in config['models']:
            for repeat in range(10):
                cells.append({'id':f'{model}--appendix-b-v1--{t["task_id"]}--r{repeat}',
                              'model':model,'variant':'appendix-b-v1','task_id':t['task_id'],
                              'problem':t['problem'],'repeat':repeat,'messages':[{'role':'user','content':message}]})
    return {'schema_version':1,'experiment':'NL-to-Ansible generation only','config':config,
            'repetitions':10,'tasks':tasks,'cells':sorted(cells,key=lambda c:ev.digest(c['id'])),
            'prompt_template':template,'sources':{'prompt_sha256':ev.digest(prompt_path.read_bytes()),
              'tasks_sha256':ev.digest(tasks),'source_references_sha256':ev.digest(Path(refs).read_bytes()),
              'generator_sha256':ev.digest(Path(__file__).read_bytes()),
              'ledger_sha256':ev.digest((REPO/'evaluation/code/matrix_run.py').read_bytes())},
            'prompt_provenance':'Appendix B verbatim text supplied by Darsh in this conversation; single user message, no added system prompt',
            'created_at':datetime.now(timezone.utc).isoformat()}


def build(cell,config):
    m=config['models'][cell['model']];p=m['provider'];effort=m['reasoning_effort']
    headers={'Content-Type':'application/json','User-Agent':'Astrogator-Evaluation/1.0'}
    if p=='openai':
        url='https://api.openai.com/v1/responses';headers['Authorization']='Bearer '+os.environ['OPENAI_API_KEY']
        body={'model':m['id'],'input':cell['messages'],'store':False,'max_output_tokens':4096,'reasoning':{'effort':effort}}
    elif p=='anthropic':
        url='https://api.anthropic.com/v1/messages';headers.update({'x-api-key':os.environ['ANTHROPIC_API_KEY'],'anthropic-version':'2023-06-01'})
        body={'model':m['id'],'messages':cell['messages'],'max_tokens':4096,'output_config':{'effort':effort}}
    else:
        assert p=='agentfanclub'
        base=os.environ['AGENTFANCLUB_BASE_URL'].rstrip('/');assert base==m['base_url'].rstrip('/')
        url=base+'/chat/completions';headers['Authorization']='Bearer '+os.environ['AGENTFANCLUB_API_KEY']
        # Stream reasoning/content to keep the router connection alive across long thinking.
        body={'model':m['id'],'messages':cell['messages'],'max_tokens':4096,'reasoning_effort':effort,
              'stream':True,'stream_options':{'include_usage':True}}
    return url,body,headers


def collect_stream(response,model):
    content=[];reasoning=[];usage=None;finish=None;returned=model;count=0;wire=hashlib.sha256();start=time.monotonic();done=False
    for line in response:
        wire.update(line)
        if time.monotonic()-start>600:raise urllib.error.URLError('stream_deadline')
        if not line.startswith(b'data:'):continue
        data=line[5:].strip()
        if data==b'[DONE]':done=True;break
        if not data:continue
        obj=json.loads(data);count+=1
        if obj.get('error'):raise urllib.error.URLError('stream_provider_error')
        returned=obj.get('model',returned)
        if obj.get('usage') is not None:usage=obj['usage']
        for choice in obj.get('choices',[]):
            delta=choice.get('delta') or {}
            if delta.get('content'):content.append(delta['content'])
            if delta.get('reasoning_content'):reasoning.append(delta['reasoning_content'])
            if choice.get('finish_reason'):finish=choice['finish_reason']
    if finish is None:raise urllib.error.URLError('stream_ended_without_finish_reason')
    return {'model':returned,'choices':[{'finish_reason':finish,'message':{'role':'assistant','content':''.join(content),'reasoning_content':''.join(reasoning)}}],
            'usage':usage,'stream_record':{'chunks':count,'wire_sha256':wire.hexdigest(),'done_marker':done}}


def request(cell,config):
    m=config['models'][cell['model']];url,body,headers=build(cell,config)
    req=urllib.request.Request(url,data=json.dumps(body).encode(),headers=headers)
    with urllib.request.urlopen(req,timeout=180) as response:
        raw=collect_stream(response,m['id']) if body.get('stream') else json.load(response)
    if m['provider']=='openai':
        text='\n'.join(x['text'] for item in raw.get('output',[]) for x in item.get('content',[]) if x.get('type')=='output_text');completed=raw.get('status')=='completed'
    elif m['provider']=='anthropic':
        text='\n'.join(x['text'] for x in raw.get('content',[]) if x.get('type')=='text');completed=raw.get('stop_reason')=='end_turn'
    else:text=raw['choices'][0]['message']['content'];completed=raw['choices'][0]['finish_reason']=='stop'
    return {'status':'completed' if completed else 'incomplete','text':text,'response':raw,
            'requested_model':m['id'],'returned_model':raw.get('model'),'usage':raw.get('usage')}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('command',choices=['freeze','run'])
    p.add_argument('--manifest',type=Path,required=True);p.add_argument('--references',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--credentials-file',type=Path)
    p.add_argument('--preflight',action='store_true',help='Attempt one planned cell per model, retaining the full immutable manifest');p.add_argument('--workers',type=int,default=16);p.add_argument('--total-budget-usd',type=float,default=25)
    p.add_argument('--anthropic-budget-usd',type=float,default=15);a=p.parse_args()
    assert 0<=a.total_budget_usd<=25 and 0<=a.anthropic_budget_usd<=15 and a.workers>0
    if a.command=='freeze':
        assert a.references;manifest=freeze(a.references);ev.write_new(a.manifest,manifest);print(json.dumps(ev.estimate(manifest),indent=2));return
    assert a.output and a.credentials_file
    allowed={'OPENAI_API_KEY','ANTHROPIC_API_KEY','AGENTFANCLUB_API_KEY','AGENTFANCLUB_BASE_URL'}
    os.environ.update({k:v for k,v in ev.load(a.credentials_file).items() if k in allowed})
    a.output.mkdir(parents=True,exist_ok=True)
    with (a.output/'.matrix.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        manifest=ev.load(a.manifest)
        if (a.output/'manifest.json').exists():assert ev.load(a.output/'manifest.json')==manifest
        else:ev.write_new(a.output/'manifest.json',manifest)
        runner=Matrix(manifest,a.output,a.total_budget_usd,a.anthropic_budget_usd,4,request,build)
        if a.preflight:
            from concurrent.futures import ThreadPoolExecutor
            chosen=[next(c for c in manifest['cells'] if c['model']==key) for key in manifest['config']['models']]
            with ThreadPoolExecutor(max_workers=6) as pool:list(pool.map(runner.process,chosen))
            print(json.dumps({'preflight':[{ 'cell':c['id'],'status':ev.load(a.output/'responses'/(c['id']+'.json'))['status'] if (a.output/'responses'/(c['id']+'.json')).exists() else 'budget_pending'} for c in chosen]}),flush=True)
        else:runner.run(a.workers)

if __name__=='__main__':main()
