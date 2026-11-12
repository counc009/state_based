#!/usr/bin/env python3
"""Explicitly authorized missing-cell fill. New ledger; no completed answer is rerun."""
import argparse,copy,fcntl,json,os,signal,subprocess,sys,threading,time
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime,timezone,timedelta
from pathlib import Path
import evaluate as ev
from matrix_run import Matrix
from dataset_validity import credentials,save
import dataset_transport as transport
from openkb_prompt import AdmissionStopped,BoundedMatrix

ROOT=ev.ROOT;BASE=ROOT/'results/2026-11-12-dataset-validity';RUN=BASE/'fill-in-2026-11-12'

def utc():return datetime.now(timezone.utc).isoformat()

def freeze():
 path=RUN/'private/generation/manifest.json'
 if path.exists():return ev.load(path)
 cells=[];origins={};before={};config=None
 for label,run in [('original',BASE),('openkb',BASE/'openkb-prompt')]:
  m=ev.load(run/'private/generation/manifest.json')
  if config is None:config=copy.deepcopy(m['config'])
  else:assert config['models']==m['config']['models']
  for c in m['cells']:
   p=run/'private/generation/responses'/(c['id']+'.json');r=ev.load(p)if p.exists()else{}
   if r.get('status')in('completed','incomplete'):
    before[label+'/'+c['id']]={'text_sha256':ev.digest(r['text'].encode()),'response_sha256':ev.digest(p.read_bytes())};continue
   assert c['model']in('opus','deepseek-v4-flash')
   assert label=='openkb'or c['model']=='deepseek-v4-flash'
   cells.append(copy.deepcopy(c));origins[c['id']]={'run':label,'relative_source_run':str(run.relative_to(BASE)),'previous_status':r.get('status','pending')}
 counts={f'{label}/{key}':sum(c['model']==key and origins[c['id']]['run']==label for c in cells)for label,key in [('openkb','opus'),('openkb','deepseek-v4-flash'),('original','deepseek-v4-flash')]}
 assert counts=={'openkb/opus':64,'openkb/deepseek-v4-flash':38,'original/deepseek-v4-flash':39},counts
 config.update(prior_cost_usd=0,prior_anthropic_cost_usd=0,total_budget_usd=6,provider_budgets_usd={'anthropic':3},max_output_tokens=32768)
 cells.sort(key=lambda c:(c['model']!='opus',ev.digest(c['id'])))
 m={'schema_version':1,'created_at':utc(),'scope':'Authorized fill of exactly141 missing cells; prior responses untouched','repetitions':1,'config':config,'cells':cells,'origins':origins,
    'execution':{'wall_clock_minutes':40,'total_budget_usd':6,'anthropic_budget_usd':3,'max_attempts':6,'deepseek_max_retries':5,'opus_workers':4,'deepseek_workers':64,'order':'Complete/admit Opus first; then DeepSeek across both source runs'},
    'sources':{'driver_sha256':ev.digest(Path(__file__).read_bytes()),'original_manifest_sha256':ev.digest(ev.load(BASE/'private/generation/manifest.json')),'openkb_manifest_sha256':ev.digest(ev.load(BASE/'openkb-prompt/private/generation/manifest.json'))}}
 save(path,m);save(RUN/'private/completed-before.json',before)
 for file in [Path(__file__),ROOT/'code/dataset_transport.py',ROOT/'code/matrix_run.py']:
  savepath=RUN/'private/source'/file.name;savepath.parent.mkdir(parents=True,exist_ok=True);savepath.write_bytes(file.read_bytes())
 print(json.dumps({'targets':counts,'unchanged_completed_outputs':len(before),'guards':{'total':6,'anthropic':3}}),flush=True)
 return m

class FillMatrix(Matrix):
 request=BoundedMatrix.request
 def __init__(self,m,out,start):
  self.deadline=datetime.fromisoformat(start['deadline_at']).timestamp();self.billing_file=out/'anthropic-billing-stop.json';self.billing=threading.Event()
  if self.billing_file.exists():self.billing.set()
  super().__init__(m,out,6,3,6,self.request,self.build)
 def build(self,c,config):
  if time.time()>=self.deadline:raise AdmissionStopped('40-minute deadline')
  if c['model']=='opus'and self.billing.is_set():raise AdmissionStopped('Anthropic billing stop')
  return transport.build(c,config)
 def process(self,c):
  try:return super().process(c)
  except AdmissionStopped:return

def child():
 credentials(Path('/tmp/astrogator-provider-env.json'));out=RUN/'private/generation';m=ev.load(out/'manifest.json');start=ev.load(RUN/'private/job-start.json')
 with(out/'.matrix.lock').open('a')as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);runner=FillMatrix(m,out,start)
  for model,workers in [('opus',4),('deepseek-v4-flash',64)]:
   print(json.dumps({'stage':model,'started_at':utc(),'workers':workers}),flush=True)
   while time.time()<runner.deadline:
    if model=='opus'and runner.billing.is_set():break
    pending=[c for c in m['cells']if c['model']==model and not(out/'responses'/(c['id']+'.json')).exists()]
    if not pending:break
    before=len(runner.state['attempts'])
    with ThreadPoolExecutor(max_workers=workers)as pool:
     for job in as_completed([pool.submit(runner.process,c)for c in pending]):job.result()
    if len(runner.state['attempts'])==before:break
   print(json.dumps({'stage':model,'finished_at':utc(),'accounted_usd':runner.spend(),'anthropic_usd':runner.spend('anthropic')}),flush=True)

def run():
 m=freeze();p=RUN/'private/job-start.json'
 if not p.exists():
  t=datetime.now(timezone.utc);ev.write_new(p,{'started_at':t.isoformat(),'deadline_at':(t+timedelta(minutes=40)).isoformat(),'wall_clock_minutes':40})
 start=ev.load(p);remaining=datetime.fromisoformat(start['deadline_at']).timestamp()-time.time();print(json.dumps(start),flush=True)
 if remaining>0:
  proc=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'child'],start_new_session=True)
  save(RUN/'private/supervisor-pid.json',{'supervisor':os.getpid(),'child':proc.pid})
  try:proc.wait(timeout=remaining)
  except subprocess.TimeoutExpired:
   os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
  save(RUN/'private/supervisor-result.json',{'finished_at':utc(),'returncode':proc.returncode,'deadline_reached':time.time()>=datetime.fromisoformat(start['deadline_at']).timestamp()})
 print(json.dumps({'generation_exited':True,'at':utc(),'finalization':'Separate offline receipt reconciliation/export'}),flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('command',choices=['freeze','run','child']);a=p.parse_args()
 if a.command=='freeze':freeze()
 elif a.command=='run':run()
 else:child()
