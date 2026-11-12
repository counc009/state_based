#!/usr/bin/env python3
"""Durable bounded parallel evaluation. No shell execution of generated code."""
import argparse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import threading
import time
import urllib.error
import evaluate as ev

TRANSIENT = {408, 409, 425, 429, *range(500,600)}


def usage_cost(result, model, reserve):
    """Token-based estimate; missing usage remains charged at the full reservation."""
    u = result.get('usage')
    if not isinstance(u, dict):
        return reserve, 'conservative_unreported_usage'
    if model['provider'] == 'anthropic':
        required = ('input_tokens', 'output_tokens')
        if not all(k in u for k in required): return reserve, 'conservative_unreported_usage'
        value = (u['input_tokens']*model['input_per_million'] +
                 u.get('cache_creation_input_tokens',0)*model.get('cache_write_per_million',model['input_per_million']) +
                 u.get('cache_read_input_tokens',0)*model.get('cached_input_per_million',model['input_per_million']) +
                 u['output_tokens']*model['output_per_million']) / 1e6
    else:
        inp = u.get('input_tokens',u.get('prompt_tokens'))
        out = u.get('output_tokens',u.get('completion_tokens'))
        if inp is None or out is None: return reserve, 'conservative_unreported_usage'
        details = u.get('input_tokens_details') or u.get('prompt_tokens_details') or {}
        cached = details.get('cached_tokens',0) or 0
        writes = details.get('cache_write_tokens',0) or 0
        value = ((inp-cached)*model['input_per_million'] +
                 cached*model.get('cached_input_per_million',model['input_per_million']) +
                 out*model['output_per_million'] +
                 writes*max(0,model.get('cache_write_per_million',model['input_per_million'])-model['input_per_million'])) / 1e6
    return value, 'reported_tokens_at_frozen_rates'


def retryable(result):
    return result['status'] in ('transport_error','interrupted_unknown_billing') or result.get('http_status') in TRANSIENT


class Matrix:
    def __init__(self, manifest, out, total=110, anthropic=22, max_attempts=4, request_fn=None, build_fn=None):
        self.manifest, self.out = manifest, out
        self.request_fn = request_fn or ev.request
        self.build_fn = build_fn or ev.build_request
        self.total, self.anthropic, self.max_attempts = total, anthropic, max_attempts
        self.lock = threading.Lock()
        self.cells = {c['id']:c for c in manifest['cells']}
        self.state = {'schema_version':1,'manifest_sha256':ev.digest(manifest),'attempts':[],
                      'prior_cost_usd':manifest['config'].get('prior_cost_usd',0.02),
                      'prior_anthropic_cost_usd':manifest['config'].get('prior_anthropic_cost_usd',0.000148)}
        self.state_path = out/'state.json'
        if self.state_path.exists(): self.state = ev.load(self.state_path)
        assert self.state['manifest_sha256'] == ev.digest(manifest)
        # Interrupted attempts remain charged at full reservation; no silent repeats.
        for a in self.state['attempts']:
            if a['status'] == 'in_flight':
                a['status'] = 'interrupted_unknown_billing'
                a['cost_usd'] = a['reserved_usd']
                a['cost_source'] = 'conservative_interrupted_unknown_billing'
                saved=self.out/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json')
                if not saved.exists():ev.write_new(saved,{**a,'text':'','usage':None,'error':'Process checkpoint/restart interrupted request; billed status unknown; charged full reservation'})
            elif a.get('http_status') in TRANSIENT and a.get('cost_usd')==0:
                a['cost_usd']=a['reserved_usd']
                a['cost_source']='conservative_unknown_gateway_billing'
        self.save()

    def save(self):
        tmp = self.state_path.with_suffix('.tmp')
        tmp.write_text(json.dumps(self.state,indent=2)+'\n')
        with tmp.open('r+') as f: f.flush();os.fsync(f.fileno())
        tmp.replace(self.state_path)

    def spend(self, provider=None):
        prior = self.state['prior_anthropic_cost_usd'] if provider=='anthropic' else (self.state['prior_cost_usd'] if provider is None else 0)
        return prior + sum(a.get('cost_usd',a['reserved_usd']) for a in self.state['attempts'] if provider is None or a['provider']==provider)

    def process(self, cell):
        terminal = self.out/'responses'/(cell['id']+'.json')
        if terminal.exists(): return
        model = self.manifest['config']['models'][cell['model']]
        provider = model['provider']
        previous = [a for a in self.state['attempts'] if a['cell_id']==cell['id']]
        if previous and not retryable(previous[-1]):
            saved=self.out/'attempts'/(cell['id']+f'--attempt{len(previous)}.json')
            if saved.exists():
                ev.write_new(terminal,ev.load(saved));return
        for attempt in range(len(previous),self.max_attempts):
            # Construct first: missing credentials/config must not reserve paid work.
            url, body, _ = self.build_fn(cell,self.manifest['config'])
            cost = ev.reserve(cell,self.manifest['config'])
            with self.lock:
                if self.spend()+cost > self.total+1e-9 or (provider=='anthropic' and self.spend(provider)+cost > self.anthropic+1e-9):
                    return  # no receipt: cell remains resumable after an accounting limit increase
                record = {'cell_id':cell['id'],'attempt':attempt+1,'provider':provider,'reserved_usd':cost,
                          'status':'in_flight','started_at':datetime.now(timezone.utc).isoformat(),
                          'request_url':url,'request_body':body}
                self.state['attempts'].append(record); self.save()
            start = time.monotonic()
            try:
                result = self.request_fn(cell,self.manifest['config'])
            except urllib.error.HTTPError as e:
                result = {'status':'provider_error','http_status':e.code,'text':'','usage':None}
                # Provider error JSON only; replace any secret strings before persistence.
                message=e.read(10000).decode(errors='replace')
                for key,value in os.environ.items():
                    if (key.endswith('_KEY') or key.endswith('_TOKEN')) and value: message=message.replace(value,'[REDACTED]')
                result['error']=message
                if e.code not in TRANSIENT: result['usage']={'input_tokens':0,'output_tokens':0}
                try: result['retry_after_s']=min(60,max(0,float(e.headers.get('Retry-After',0))))
                except ValueError: pass
            except Exception as e:
                result = {'status':'transport_error','error':type(e).__name__,'text':'','usage':None}
            result.update(cell_id=cell['id'],attempt=attempt+1,seconds=round(time.monotonic()-start,6),
                          request_url=url,request_body=body)
            charged, source = usage_cost(result,model,cost)
            result.update(cost_usd=charged,cost_source=source,reserved_usd=cost)
            ev.write_new(self.out/'attempts'/(cell['id']+f'--attempt{attempt+1}.json'),result)
            with self.lock:
                record.update(status=result['status'],cost_usd=charged,cost_source=source,seconds=result['seconds'],http_status=result.get('http_status'))
                self.save()
                progress={'cell':cell['id'],'attempt':attempt+1,'status':result['status'],
                          'spent_usd':round(self.spend(),6),'anthropic_usd':round(self.spend('anthropic'),6)}
            print(json.dumps(progress),flush=True)
            if not retryable(result) or attempt+1>=self.max_attempts:
                ev.write_new(terminal,result);return
            time.sleep(max(result.get('retry_after_s',0),min(60,2**(attempt+1))))
        if not terminal.exists() and previous:
            last=self.out/'attempts'/(cell['id']+f'--attempt{len(previous)}.json')
            if last.exists():ev.write_new(terminal,ev.load(last))

    def run(self, workers):
        while True:
            before=len(self.state['attempts'])
            with ThreadPoolExecutor(max_workers=workers) as pool:
                jobs=[pool.submit(self.process,c) for c in self.manifest['cells']]
                for job in as_completed(jobs):job.result()
            if len(self.state['attempts'])==before:break
        terminal=sum((self.out/'responses'/(c['id']+'.json')).exists() for c in self.manifest['cells'])
        result={'planned':len(self.cells),'terminal':terminal,'pending':len(self.cells)-terminal,
                'attempts':len(self.state['attempts']),'accounted_usd':self.spend(),
                'anthropic_accounted_usd':self.spend('anthropic'),
                'total_limit_usd':self.total,'anthropic_limit_usd':self.anthropic}
        (self.out/'run-status.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--workers',type=int,default=12);p.add_argument('--total-budget-usd',type=float,default=110)
    p.add_argument('--anthropic-budget-usd',type=float,default=22)
    p.add_argument('--max-attempts',type=int,default=4)
    p.add_argument('--credentials-file',type=Path,help='Private JSON of model-provider credentials; never published')
    a=p.parse_args();assert a.workers>0 and a.max_attempts>0 and 0<=a.total_budget_usd<=110 and a.anthropic_budget_usd>=0
    if a.credentials_file:
        allowed={'OPENAI_API_KEY','ANTHROPIC_API_KEY','AGENTFANCLUB_API_KEY','AGENTFANCLUB_BASE_URL'}
        values=ev.load(a.credentials_file)
        os.environ.update({k:v for k,v in values.items() if k in allowed})
    a.output.mkdir(parents=True,exist_ok=True)
    with (a.output/'.matrix.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        m=ev.load(a.manifest)
        if (a.output/'manifest.json').exists():assert ev.load(a.output/'manifest.json')==m
        else:ev.write_new(a.output/'manifest.json',m)
        Matrix(m,a.output,a.total_budget_usd,a.anthropic_budget_usd,a.max_attempts).run(a.workers)

if __name__=='__main__':main()
